/* ============================================================
   OMR SCANNER - app.js
   Quy trình: Camera -> OpenCV ->
   Tìm 4 ô vuông đen ở góc phiếu (ưu tiên) hoặc dò viền tờ giấy
   (dự phòng) -> Kiểm tra ổn định -> Warp Perspective ->
   Upload (base64) lên Google Apps Script -> Google Drive
   ============================================================ */

// ---------- Phần tử DOM ----------
const video       = document.getElementById('video');
const overlay     = document.getElementById('overlay');
const canvas      = document.getElementById('canvas');   // canvas xử lý (độ phân giải nhỏ)
const resultCanvas= document.getElementById('result');    // canvas ảnh sau khi duỗi thẳng
const statusEl    = document.getElementById('status');
const captureBtn  = document.getElementById('capture');
const autoBtn     = document.getElementById('autoToggle');
const previewBox  = document.getElementById('preview');
const previewImg  = document.getElementById('previewImg');
const uploadStatusEl = document.getElementById('uploadStatus');
const retakeBtn   = document.getElementById('retake');
const dupModal        = document.getElementById('dupModal');
const dupMessageEl    = document.getElementById('dupMessage');
const dupOverwriteBtn = document.getElementById('dupOverwriteBtn');
const dupCancelBtn    = document.getElementById('dupCancelBtn');

const overlayCtx = overlay.getContext('2d');

// ---------- Cấu hình thuật toán ----------
const PROC_WIDTH        = 640;   // độ rộng ảnh xử lý (tăng lên để 4 ô vuông góc đủ lớn để nhận ra)
const PROCESS_INTERVAL  = 90;    // ms NGHỈ giữa 2 lần xử lý (tính sau khi xử lý xong, nên máy chậm không bị dồn việc)
const MIN_AREA_RATIO    = 0.10;  // phiếu phải chiếm tối thiểu 10% diện tích khung hình
const ASPECT_TARGETS    = [210/297, 297/210]; // A4 dọc và ngang
const ASPECT_TOLERANCE  = 0.22;
const STABLE_WINDOW_MS  = 600;   // phiếu phải đứng yên ít nhất ~0,5s (tính theo THỜI GIAN, không đếm số khung hình)
const STABLE_PIXEL_TOL  = 14;    // sai lệch tối đa (px) giữa các khung (tăng từ 8 để chịu được tay rung nhẹ)
const CAPTURE_COOLDOWN  = 2500;  // ms khoá lại sau khi vừa chụp, tránh chụp liên tục
const OUT_W = 1240, OUT_H = 1754; // kích thước ảnh xuất ra (~A4 150dpi)

// Cấu hình riêng cho nhận diện 4 Ô VUÔNG ĐEN Ở GÓC (marker) - phương pháp chính
// Phiếu trả lời có in sẵn 4 ô vuông đen nhỏ ở 4 góc để căn chỉnh, đáng tin cậy
// hơn nhiều so với việc dò viền cả tờ giấy (không bị ảnh hưởng bởi nền phía sau).
const MARKER_MIN_SIDE_RATIO = 0.010; // cạnh ô vuông tối thiểu, tính theo % chiều rộng ảnh xử lý
const MARKER_MAX_SIDE_RATIO = 0.10;  // cạnh ô vuông tối đa
const MARKER_ASPECT_MIN     = 0.60;  // ô vuông thật sẽ có tỉ lệ cạnh gần 1:1 (nới ra để chịu mờ/nghiêng nhẹ)
const MARKER_ASPECT_MAX     = 1.67;
const MARKER_MIN_EXTENT     = 0.70;  // độ "đặc" của khối (ô vuông 10px chỉ đo được ~0.8)
const MARKER_ASPECT_TOL     = 0.12;  // khung 4 ô vuông phải có tỉ lệ A4 (sai số 12%) - nếu thiếu 1 góc sẽ bị loại

// ---------- Biến trạng thái ----------
let cvReady = false;
let procCanvas = document.createElement('canvas');
let procCtx = procCanvas.getContext('2d');
let lastQuadProc = null;     // góc phiếu mới nhất (toạ độ hệ xử lý)
let history = [];            // lịch sử {t, pts} để kiểm tra ổn định
let autoCaptureEnabled = true;
let lockedUntil = 0;         // thời điểm hết khoá sau khi chụp
let loopTimer = null;
let fullCanvas = null;       // canvas chụp ảnh gốc, DÙNG LẠI mỗi lần quét (tránh rò bộ nhớ trên điện thoại)
let isBusy = false;
let lastMarkerDebug = { candidates: [] }; // để hiển thị debug: các ô vuông đang "nhìn thấy"

// SBD đã quét THÀNH CÔNG trong phiên làm việc này (mất khi tải lại trang).
// Dùng để cảnh báo ngay lúc quét nếu 2 phiếu khác nhau lại ra cùng 1 SBD
// (khả năng cao là 1 trong 2 học sinh tô nhầm số báo danh).
const scannedSBDs = new Set();

// ============================================================
// BƯỚC 1-3: MỞ CAMERA
// ============================================================
async function startCamera() {
  try {
    const stream = await navigator.mediaDevices.getUserMedia({
      video: { facingMode: 'environment', width: { ideal: 1280 }, height: { ideal: 720 } },
      audio: false
    });
    video.srcObject = stream;
    await video.play();
    resizeCanvases();
    window.addEventListener('resize', resizeCanvases);
    setStatus('Đang tải công cụ xử lý ảnh (opencv.js)... 0s');
    waitForOpenCV();
  } catch (err) {
    setStatus('Không mở được camera: ' + err.message);
  }
}

function resizeCanvases() {
  overlay.width  = window.innerWidth;
  overlay.height = window.innerHeight;

  const scale = PROC_WIDTH / video.videoWidth;
  procCanvas.width  = PROC_WIDTH;
  procCanvas.height = Math.round(video.videoHeight * scale);
}

// ============================================================
// Chờ OpenCV.js tải xong (script async trong index.html)
// ============================================================
let openCvWaitMs = 0;
let openCvInitStarted = false;

function waitForOpenCV() {
  if (typeof window.cv === 'undefined') {
    pollAgain();
    return;
  }

  // Bản build "MODULARIZE" (như @techstark/opencv-js): window.cv là một PROMISE
  // (không phải object dùng ngay được) — phải .then() để lấy công cụ OpenCV thật.
  if (window.cv instanceof Promise) {
    if (!openCvInitStarted) {
      openCvInitStarted = true;
      window.cv.then((resolvedCv) => {
        window.cv = resolvedCv; // ghi đè lại biến cv để phần code còn lại dùng bình thường
        onOpenCVReady();
      }).catch((err) => {
        setStatus('⚠ Lỗi khởi tạo opencv.js: ' + err.message, false);
        console.error('opencv init error:', err);
      });
    }
    return; // đang chờ Promise ở trên resolve, không cần poll thêm
  }

  // Bản build "thường" (docs.opencv.org gốc): cv là object có sẵn thuộc tính
  if (cv.Mat) {
    onOpenCVReady();
  } else if (!openCvInitStarted) {
    openCvInitStarted = true;
    cv.onRuntimeInitialized = onOpenCVReady;
  }
}

function pollAgain() {
  openCvWaitMs += 200;
  setStatus(`Đang tải công cụ xử lý ảnh (opencv.js)... ${Math.round(openCvWaitMs / 1000)}s`);
  if (openCvWaitMs > 25000) {
    setStatus('⚠ Không tải được opencv.js sau 25s (kiểm tra lại mạng / file trên GitHub)', false);
    return; // ngừng thử lại, tránh vòng lặp vô tận âm thầm
  }
  setTimeout(waitForOpenCV, 200);
}

function onOpenCVReady() {
  cvReady = true;
  setStatus('Đưa phiếu vào khung hình');
  // Tự hẹn giờ lại SAU KHI xử lý xong 1 khung (thay vì setInterval) để máy chậm không bị dồn việc
  const loop = () => {
    processFrame();
    loopTimer = setTimeout(loop, PROCESS_INTERVAL);
  };
  loop();
}

// ============================================================
// BƯỚC 6, 11-19: XỬ LÝ TỪNG KHUNG HÌNH
// Gray -> Blur -> Canny -> FindContours -> Polygon 4 góc -> Kiểm tra tỉ lệ
// ============================================================
function processFrame() {
  if (!cvReady || isBusy || video.readyState < 2) return;
  if (Date.now() < lockedUntil) return; // đang trong thời gian khoá sau khi chụp

  procCtx.drawImage(video, 0, 0, procCanvas.width, procCanvas.height);

  const frameArea = procCanvas.width * procCanvas.height;
  let src, gray;
  try {
    src = cv.imread(procCanvas);
    gray = new cv.Mat();
    cv.cvtColor(src, gray, cv.COLOR_RGBA2GRAY);

    // Chỉ dùng 4 ô vuông đen ở góc phiếu. Thiếu 1 góc là KHÔNG chụp (tránh lệch lưới
    // làm đọc sai/bỏ sót câu). Đã bỏ cách dự phòng dò viền giấy vì nặng và kém chính xác.
    const quad = findMarkerQuad(gray, frameArea);

    if (quad) {
      lastQuadProc = quad;
      drawOverlay(quad, true);
      trackStability(quad);
    } else {
      lastQuadProc = null;
      drawOverlay(null, false); // vẫn vẽ các chấm vàng debug (ô vuông đã thấy nhưng chưa đủ 4)
      history = [];
      const n = lastMarkerDebug.candidates.length;
      setStatus(`Chưa thấy đủ 4 ô vuông góc (thấy ${n}) - hãy lùi máy, chừa lề quanh phiếu`, false);
    }
  } catch (err) {
    // QUAN TRỌNG: hiện lỗi thật ra màn hình thay vì để lỗi ẩn trong console
    // (nếu không có dòng này, khi có lỗi JS thì trạng thái sẽ bị "đứng hình" mãi mãi)
    setStatus('⚠ Lỗi xử lý: ' + err.message, false);
    console.error('processFrame error:', err);
  } finally {
    // Giải phóng bộ nhớ OpenCV (bắt buộc, tránh rò rỉ)
    [src, gray].forEach(m => m && m.delete && m.delete());
  }
}

// ============================================================
// PHƯƠNG PHÁP CHÍNH: tìm 4 ô vuông đen in sẵn ở góc phiếu
// (đáng tin cậy hơn dò viền giấy vì tương phản đen/trắng rất mạnh,
// không bị ảnh hưởng bởi hoa văn của mặt bàn/sàn nhà phía sau phiếu)
// ============================================================
function findMarkerQuad(gray, frameArea) {
  let bin, smoothed, contours, hierarchy;
  try {
    // Làm mượt nhẹ trước khi nhị phân hoá: giúp thuật toán chịu được ảnh hơi
    // rung/mờ (motion blur nhẹ, nhiễu hạt do thiếu sáng) mà vẫn giữ được cạnh
    // ô vuông rõ ràng (median blur giữ cạnh tốt hơn Gaussian thông thường)
    smoothed = new cv.Mat();
    cv.medianBlur(gray, smoothed, 3);

    // Nhị phân hoá ảnh: vùng tối (chữ, ô vuông đen) -> trắng, còn lại -> đen
    bin = new cv.Mat();
    cv.threshold(smoothed, bin, 0, 255, cv.THRESH_BINARY_INV + cv.THRESH_OTSU);

    contours = new cv.MatVector();
    hierarchy = new cv.Mat();
    cv.findContours(bin, contours, hierarchy, cv.RETR_EXTERNAL, cv.CHAIN_APPROX_SIMPLE); // EXTERNAL: ít đường viền hơn -> nhanh hơn

    const w = gray.cols;
    const minSide = w * MARKER_MIN_SIDE_RATIO;
    const maxSide = w * MARKER_MAX_SIDE_RATIO;

    const candidates = [];
    for (let i = 0; i < contours.size(); i++) {
      const cnt = contours.get(i);
      const rect = cv.boundingRect(cnt);
      const area = cv.contourArea(cnt);
      const boxArea = rect.width * rect.height;

      if (rect.width >= minSide && rect.width <= maxSide &&
          rect.height >= minSide && rect.height <= maxSide && boxArea > 0) {
        const aspect = rect.width / rect.height;
        const extent = area / boxArea; // độ "đặc": ô vuông tô đen đặc ~1.0, vòng tròn/chữ thấp hơn
        if (aspect >= MARKER_ASPECT_MIN && aspect <= MARKER_ASPECT_MAX && extent >= MARKER_MIN_EXTENT) {
          candidates.push({
            x: rect.x + rect.width / 2,
            y: rect.y + rect.height / 2,
            size: (rect.width + rect.height) / 2
          });
        }
      }
      cnt.delete();
    }

    if (candidates.length < 4) {
      lastMarkerDebug.candidates = candidates;
      return null;
    }

    lastMarkerDebug.candidates = candidates;

    // 4 ô vuông góc luôn là các điểm CỰC TRỊ (trên-trái, trên-phải, dưới-phải, dưới-trái)
    const sums  = candidates.map(c => c.x + c.y);
    const diffs = candidates.map(c => c.y - c.x);
    const idx = [
      sums.indexOf(Math.min(...sums)),    // trên-trái
      diffs.indexOf(Math.min(...diffs)),  // trên-phải
      sums.indexOf(Math.max(...sums)),    // dưới-phải
      diffs.indexOf(Math.max(...diffs))   // dưới-trái
    ];
    if (new Set(idx).size < 4) return null; // 1 khối bị chọn làm 2 góc -> thiếu góc

    // 4 ô vuông in cùng kích thước: nếu có khối lệch cỡ (vd chữ, ô đen to của bảng SBD) -> thiếu 1 góc thật
    const corners = idx.map(i => candidates[i]);
    const sz = corners.map(c => c.size).sort((a, b) => a - b);
    const medSize = (sz[1] + sz[2]) / 2;
    if (corners.some(c => c.size < medSize * 0.7 || c.size > medSize * 1.4)) return null;

    const ordered = corners.map(c => ({ x: c.x, y: c.y }));

    // Diện tích đủ lớn + tỉ lệ khung 4 ô vuông phải gần A4 (siết chặt hơn trước)
    if (polygonArea(ordered) < frameArea * MIN_AREA_RATIO) return null;
    if (!aspectRatioOk(ordered, MARKER_ASPECT_TOL)) return null;

    return ordered;
  } finally {
    [bin, smoothed, contours, hierarchy].forEach(m => m && m.delete && m.delete());
  }
}

function polygonArea(pts) {
  let area = 0;
  for (let i = 0; i < pts.length; i++) {
    const p1 = pts[i], p2 = pts[(i + 1) % pts.length];
    area += p1.x * p2.y - p2.x * p1.y;
  }
  return Math.abs(area / 2);
}

// BƯỚC 16-18: chọn contour lớn nhất, xấp xỉ 4 góc, kiểm tra diện tích + tỉ lệ
function findBestQuad(contours, frameArea) {
  let best = null;
  let bestArea = 0;

  for (let i = 0; i < contours.size(); i++) {
    const cnt = contours.get(i);
    const area = cv.contourArea(cnt);

    if (area > bestArea && area > frameArea * MIN_AREA_RATIO) {
      const peri = cv.arcLength(cnt, true);
      const approx = new cv.Mat();
      cv.approxPolyDP(cnt, approx, 0.02 * peri, true);

      if (approx.rows === 4 && cv.isContourConvex(approx)) {
        const pts = matToPoints(approx);
        const ordered = orderPoints(pts);
        if (aspectRatioOk(ordered)) {
          bestArea = area;
          best = ordered;
        }
      }
      approx.delete();
    }
    cnt.delete();
  }
  return best;
}

function matToPoints(mat) {
  const data = mat.data32S;
  const pts = [];
  for (let i = 0; i < data.length; i += 2) {
    pts.push({ x: data[i], y: data[i + 1] });
  }
  return pts;
}

// Sắp xếp 4 điểm theo thứ tự: trên-trái, trên-phải, dưới-phải, dưới-trái
function orderPoints(pts) {
  const sum = pts.map(p => p.x + p.y);
  const diff = pts.map(p => p.y - p.x);
  const tl = pts[sum.indexOf(Math.min(...sum))];
  const br = pts[sum.indexOf(Math.max(...sum))];
  const tr = pts[diff.indexOf(Math.min(...diff))];
  const bl = pts[diff.indexOf(Math.max(...diff))];
  return [tl, tr, br, bl];
}

// BƯỚC 18: kiểm tra tỉ lệ khung gần với A4 (0.707) ở cả 2 chiều
function aspectRatioOk([tl, tr, br, bl], tol = ASPECT_TOLERANCE) {
  const widthTop    = dist(tl, tr);
  const widthBottom  = dist(bl, br);
  const heightLeft   = dist(tl, bl);
  const heightRight  = dist(tr, br);
  const w = (widthTop + widthBottom) / 2;
  const h = (heightLeft + heightRight) / 2;
  if (w < 10 || h < 10) return false;
  const ratio = w / h;
  return ASPECT_TARGETS.some(t => Math.abs(ratio - t) < t * tol);
}

function dist(a, b) {
  return Math.hypot(a.x - b.x, a.y - b.y);
}

// ============================================================
// BƯỚC 19: VẼ KHUNG XANH LÊN OVERLAY (đổi toạ độ proc -> hiển thị)
// ============================================================
function drawOverlay(quadProc, locked) {
  clearOverlay();

  // Vẽ chấm VÀNG debug tại các ô vuông ứng viên đã tìm thấy (để biết thuật toán đang "nhìn" thấy gì)
  lastMarkerDebug.candidates.forEach(c => {
    const p = procToOverlay(c);
    overlayCtx.beginPath();
    overlayCtx.arc(p.x, p.y, 8, 0, Math.PI * 2);
    overlayCtx.strokeStyle = '#facc15';
    overlayCtx.lineWidth = 3;
    overlayCtx.stroke();
  });

  if (!quadProc) return;

  const pts = quadProc.map(p => procToOverlay(p));

  overlayCtx.beginPath();
  overlayCtx.moveTo(pts[0].x, pts[0].y);
  for (let i = 1; i < pts.length; i++) overlayCtx.lineTo(pts[i].x, pts[i].y);
  overlayCtx.closePath();
  overlayCtx.strokeStyle = '#22c55e';
  overlayCtx.lineWidth = 4;
  overlayCtx.stroke();

  pts.forEach(p => {
    overlayCtx.beginPath();
    overlayCtx.arc(p.x, p.y, 6, 0, Math.PI * 2);
    overlayCtx.fillStyle = '#22c55e';
    overlayCtx.fill();
  });
}

function clearOverlay() {
  overlayCtx.clearRect(0, 0, overlay.width, overlay.height);
}

// Video hiển thị bằng object-fit:cover -> phải quy đổi toạ độ đúng cách
function procToOverlay(p) {
  const scaleProcToVideo = video.videoWidth / procCanvas.width;
  const videoX = p.x * scaleProcToVideo;
  const videoY = p.y * scaleProcToVideo;

  const coverScale = Math.max(overlay.width / video.videoWidth, overlay.height / video.videoHeight);
  const offsetX = (overlay.width  - video.videoWidth  * coverScale) / 2;
  const offsetY = (overlay.height - video.videoHeight * coverScale) / 2;

  return {
    x: videoX * coverScale + offsetX,
    y: videoY * coverScale + offsetY
  };
}

// ============================================================
// BƯỚC 20: KIỂM TRA ĐỘ ỔN ĐỊNH (chống rung tay)
// ============================================================
function trackStability(quad) {
  const now = Date.now();
  history.push({ t: now, pts: quad });
  history = history.filter(h => now - h.t <= STABLE_WINDOW_MS + 200);

  // Phải có dữ liệu đủ lâu (theo thời gian), không phụ thuộc máy xử lý nhanh hay chậm
  const span = now - history[0].t;
  if (history.length < 2 || span < STABLE_WINDOW_MS * 0.8) {
    setStatus('Đang căn chỉnh...', false);
    return;
  }

  // Mọi khung trong cửa sổ phải gần với khung mới nhất
  const last = history[history.length - 1].pts;
  let maxMove = 0;
  for (const h of history) {
    for (let i = 0; i < 4; i++) maxMove = Math.max(maxMove, dist(h.pts[i], last[i]));
  }

  if (maxMove <= STABLE_PIXEL_TOL) {
    setStatus('✔ Đã ổn định', true);
    if (autoCaptureEnabled && Date.now() >= lockedUntil) {
      triggerCapture();
    }
  } else {
    setStatus('Giữ yên máy...', false);
  }
}

function setStatus(text, locked) {
  statusEl.textContent = text;
  statusEl.classList.toggle('locked', !!locked);
}

// ============================================================
// BƯỚC 5-onward: CHỤP + WARP PERSPECTIVE (duỗi thẳng phiếu)
// ============================================================
function triggerCapture() {
  if (isBusy) return;
  if (!lastQuadProc) {
    alert('Chưa nhận diện được phiếu. Hãy đưa phiếu vào giữa khung hình.');
    return;
  }
  isBusy = true;
  lockedUntil = Date.now() + CAPTURE_COOLDOWN;

  // Chụp ở ĐỘ PHÂN GIẢI GỐC của camera để ảnh nét, không dùng canvas nhỏ đã xử lý
  if (!fullCanvas) fullCanvas = document.createElement('canvas'); // dùng lại 1 canvas duy nhất
  fullCanvas.width = video.videoWidth;
  fullCanvas.height = video.videoHeight;
  fullCanvas.getContext('2d').drawImage(video, 0, 0);

  // Quy đổi 4 góc từ toạ độ xử lý (proc) sang toạ độ độ phân giải gốc
  const scaleProcToVideo = video.videoWidth / procCanvas.width;
  const quadFull = lastQuadProc.map(p => ({ x: p.x * scaleProcToVideo, y: p.y * scaleProcToVideo }));

  warpAndShow(fullCanvas, quadFull);
}

function warpAndShow(fullCanvas, quadFull) {
  let src, dst, M, srcTri, dstTri;
  try {
    src = cv.imread(fullCanvas);
    dst = new cv.Mat();

    srcTri = cv.matFromArray(4, 1, cv.CV_32FC2, [
      quadFull[0].x, quadFull[0].y,
      quadFull[1].x, quadFull[1].y,
      quadFull[2].x, quadFull[2].y,
      quadFull[3].x, quadFull[3].y
    ]);
    dstTri = cv.matFromArray(4, 1, cv.CV_32FC2, [
      0, 0,  OUT_W, 0,  OUT_W, OUT_H,  0, OUT_H
    ]);

    M = cv.getPerspectiveTransform(srcTri, dstTri);
    cv.warpPerspective(src, dst, M, new cv.Size(OUT_W, OUT_H));

    resultCanvas.width = OUT_W;
    resultCanvas.height = OUT_H;
    cv.imshow(resultCanvas, dst);

    // Kiểm tra ngay các khối Số báo danh / Mã Đề / Phần I trên ảnh vừa duỗi thẳng
    const ctx2d = resultCanvas.getContext('2d');
    prepareSheet(ctx2d, OUT_W, OUT_H); // tự căn lưới + mức nền cho riêng phiếu này
    const sbdCheck = checkSBDGrid(ctx2d, OUT_W, OUT_H);
    const madeCheck = checkMadeGrid(ctx2d, OUT_W, OUT_H);
    const phan1Check = checkPhan1Grid(ctx2d, OUT_W, OUT_H);

    showPreviewAndUpload(sbdCheck, madeCheck, phan1Check);
  } finally {
    [src, dst, M, srcTri, dstTri].forEach(m => m && m.delete && m.delete());
    isBusy = false;
  }
}

// Một số trình duyệt (đặc biệt trên điện thoại) chặn phát âm thanh
// cho tới khi có cử chỉ chạm đầu tiên của người dùng -> "mở khoá" ở đây
function unlockAudioOnce() {
  if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
  audioCtx.resume().then(() => {
    audioUnlocked = true;
    const hint = document.getElementById('audioHint');
    if (hint) hint.remove();
  });
  document.removeEventListener('touchstart', unlockAudioOnce);
  document.removeEventListener('click', unlockAudioOnce);
}
document.addEventListener('touchstart', unlockAudioOnce, { once: true });
document.addEventListener('click', unlockAudioOnce, { once: true });

// Nút chụp thủ công
captureBtn.addEventListener('click', () => {
  if (lastQuadProc) {
    triggerCapture();
  } else {
    // Không có khung nhận diện -> vẫn cho chụp nguyên khung hình để người dùng tự xử lý
    alert('Chưa thấy phiếu rõ nét. Hãy chỉnh lại góc chụp rồi thử lại.');
  }
});

autoBtn.addEventListener('click', () => {
  autoCaptureEnabled = !autoCaptureEnabled;
  autoBtn.textContent = 'Tự động: ' + (autoCaptureEnabled ? 'BẬT' : 'TẮT');
});

retakeBtn.addEventListener('click', () => {
  previewBox.classList.add('hidden');
  history = [];
  lockedUntil = 0;
  setStatus('Đưa phiếu vào khung hình', false);
});

// ============================================================
// ÂM THANH PHẢN HỒI (giống máy quét mã vạch siêu thị)
// ============================================================
let audioCtx = null;
let audioUnlocked = false;

function playBeep(freq = 1200, durationMs = 120) {
  try {
    if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();

    // QUAN TRỌNG: nếu AudioContext chưa được "mở khoá" bằng cử chỉ chạm của
    // người dùng, trình duyệt sẽ GIỮ LẠI âm thanh và chỉ phát trễ vào lần
    // chạm đầu tiên sau đó (gây cảm giác "kêu trễ", ví dụ kêu sau khi upload
    // xong vì lúc đó người dùng mới chạm vào màn hình). Để tránh việc này,
    // nếu chưa mở khoá thì bỏ qua không phát (chỉ rung), thay vì phát trễ.
    if (!audioUnlocked || audioCtx.state === 'suspended') {
      console.warn('Âm thanh chưa được mở khoá (cần chạm màn hình 1 lần) -> bỏ qua, chỉ rung.');
      return;
    }

    const osc = audioCtx.createOscillator();
    const gain = audioCtx.createGain();
    osc.type = 'sine';
    osc.frequency.value = freq;
    gain.gain.value = 0.25; // âm lượng vừa phải, tránh giật mình
    osc.connect(gain);
    gain.connect(audioCtx.destination);
    osc.start();
    osc.stop(audioCtx.currentTime + durationMs / 1000);
  } catch (err) {
    console.warn('Không phát được âm thanh:', err.message);
  }
}

// "Tít" 1 tiếng ngắn, cao -> quét/lưu THÀNH CÔNG
function feedbackSuccess() {
  playBeep(1400, 100);
  if (navigator.vibrate) navigator.vibrate(60); // rung nhẹ 1 lần
}

// "Tè tè" 2 tiếng liên tiếp, trầm hơn -> CẢNH BÁO cần dừng kiểm tra
function feedbackWarning() {
  playBeep(500, 150);
  setTimeout(() => playBeep(500, 150), 200);
  if (navigator.vibrate) navigator.vibrate([120, 80, 120]); // rung 2 nhịp dài
}

// ============================================================
// TOẠ ĐỘ CÁC Ô TRÒN TRÊN PHIẾU (đo từ file mẫu 132.docx, tính theo
// tỉ lệ % so với khung ảnh đã duỗi thẳng - khớp với 4 marker góc,
// nên áp dụng đúng cho MỌI kích thước OUT_W/OUT_H)
// ============================================================
// LƯU Ý QUAN TRỌNG: warpPerspective() ở trên ánh xạ TÂM của 4 ô vuông
// đen ở góc phiếu (không phải 4 góc tờ giấy) thành 4 góc của ảnh
// OUT_W x OUT_H. Vì vậy các toạ độ % bên dưới PHẢI được tính theo hệ
// "khung tâm 4 marker" (marker-to-marker), KHÔNG phải theo toàn bộ
// trang giấy kể cả phần lề ngoài 4 marker - nếu không, cả lưới sẽ bị
// lệch (đã từng xảy ra: dùng nhầm hệ toạ độ trang giấy đầy đủ khi làm
// phiếu 40 câu, khiến các ô đọc sai vị trí dù học sinh tô đúng).
const OMR_TEMPLATE = {
  // Số báo danh: 6 cột (mỗi cột 1 chữ số), 10 hàng (chữ số 0-9)
  sbd: {
    cols: [0.58961, 0.62545, 0.66129, 0.69713, 0.73297, 0.76882],
    rows: [0.11718, 0.13681, 0.15644, 0.17607, 0.19571, 0.21534, 0.23497, 0.25460, 0.27423, 0.29387]
  },
  // Mã đề: 3 cột, 10 hàng (dùng chung hàng với Số báo danh)
  made: {
    cols: [0.86738, 0.90323, 0.93907],
    rows: [0.11718, 0.13681, 0.15644, 0.17607, 0.19571, 0.21534, 0.23497, 0.25460, 0.27423, 0.29387]
  },
  // Phần I trắc nghiệm: 40 câu, chia 2 CỘT song song trên cùng 1 trang
  // (cột trái = câu 1-20, cột phải = câu 21-40), mỗi cột 4 ô A/B/C/D.
  // 2 cột dùng CHUNG 1 danh sách hàng (rows) vì được in ngang hàng nhau
  // trên phiếu - khớp với sheet_40cau (xem gen_sheet.py).
  phan1: {
    colsLeft:  [0.07885, 0.11380, 0.14875, 0.18369], // câu 1-20 (A/B/C/D)
    colsRight: [0.58065, 0.61559, 0.65054, 0.68548], // câu 21-40 (A/B/C/D)
    rows: [0.35153, 0.37117, 0.39080, 0.41043, 0.43006, 0.44969, 0.46933, 0.48896, 0.50859, 0.52822,
           0.55644, 0.57607, 0.59571, 0.61534, 0.63497, 0.65460, 0.67423, 0.69387, 0.71350, 0.73313]
  },
  bubbleRadiusFrac: 0.00896, // bán kính lấy mẫu (tính theo % chiều rộng OUT_W), nhỏ hơn ô thật để không dính viền
  // Nhận diện ô đã tô theo MỨC NỀN của từng phiếu (độ tối trung bình của giấy trắng + viền ô
  // trong ảnh vừa chụp), nên ảnh xám/có bóng không làm sai ngưỡng:
  //   minOver : ô đậm nhất phải đậm hơn mức nền ít nhất bằng này
  //   ratio   : ô đậm-nhì phải gần mức nền: (nhất - nhì) >= ratio * (nhất - nền).
  //             Ô tô đơn có tỉ lệ ~1.0; tô đôi chỉ ~0.1 -> để trống (như trước).
  minOver: 10,
  ratio: 0.5,
  // Số câu thực sự in trên phiếu. Phiếu hiện chỉ có 20 câu (cột trái); cột phải (câu 21-40)
  // không có ô tròn nên trước đây đọc nhầm chữ in/chữ viết tay thành đáp án rác.
  // Nếu sau này in phiếu đủ 40 câu thì đổi thành 40.
  activeQuestions: 20,
  // Lấy mẫu & tự căn lưới (đơn vị: pixel trên ảnh OUT_W x OUT_H)
  discRadius: 7,     // chỉ đo phần LÒNG ô tròn (bỏ viền in sẵn) -> bắt được cả ô tô nhạt
  ringRadius: 11,    // bán kính viền ô tròn in sẵn, dùng để dò độ lệch lưới
  searchRange: 16    // dò độ lệch lưới tối đa ±16px mỗi chiều
};

// Mức nền của phiếu đang đọc (tính 1 lần cho mỗi phiếu trong prepareSheet)
let currentBaseline = 0;

// Ảnh xám của phiếu đã duỗi thẳng (đọc từ canvas 1 lần/phiếu, rồi mọi phép đo dùng mảng này)
let sheetGray = null; // { data: Uint8Array, w, h }

function buildSheetGray(ctx, w, h) {
  const img = ctx.getImageData(0, 0, w, h).data;
  const g = new Uint8Array(w * h);
  for (let i = 0, j = 0; j < g.length; i += 4, j++) {
    g[j] = (img[i] + img[i + 1] + img[i + 2]) / 3;
  }
  sheetGray = { data: g, w, h };
}

// Các điểm (dx, dy) nằm trong hình tròn bán kính r
function discOffsets(r) {
  const pts = [];
  for (let dy = -r; dy <= r; dy++) {
    for (let dx = -r; dx <= r; dx++) {
      if (dx * dx + dy * dy <= r * r) pts.push([dx, dy]);
    }
  }
  return pts;
}
const DISC_PTS = discOffsets(OMR_TEMPLATE.discRadius);

// Độ tối trung bình (0 = trắng, 255 = đen) của LÒNG ô tròn quanh (cx, cy)
function sampleBubbleDarkness(cx, cy) {
  const { data, w, h } = sheetGray;
  const x0 = Math.round(cx), y0 = Math.round(cy);
  let sum = 0, count = 0;
  for (const [dx, dy] of DISC_PTS) {
    const x = x0 + dx, y = y0 + dy;
    if (x < 0 || y < 0 || x >= w || y >= h) continue;
    sum += 255 - data[y * w + x];
    count++;
  }
  return count > 0 ? sum / count : 0;
}

// Điểm khớp: trung bình độ tối dọc theo VIỀN (đường tròn bán kính R) của mọi ô trong khối,
// khi dịch lưới thêm (dx, dy). Lưới khớp đúng viền in sẵn thì điểm cao nhất.
const RING_PTS = Array.from({ length: 12 }, (_, k) => {
  const a = (k / 12) * Math.PI * 2;
  return [Math.round(OMR_TEMPLATE.ringRadius * Math.cos(a)), Math.round(OMR_TEMPLATE.ringRadius * Math.sin(a))];
}); // tính sẵn 1 lần (nhanh hơn gọi cos/sin hàng trăm nghìn lần)
function ringScore(cells, dx, dy) {
  const { data, w, h } = sheetGray;
  let total = 0;
  for (const [cx, cy] of cells) {
    const bx = Math.round(cx + dx), by = Math.round(cy + dy);
    for (const [ox, oy] of RING_PTS) {
      const x = bx + ox, y = by + oy;
      if (x < 0 || y < 0 || x >= w || y >= h) continue;
      total += 255 - data[y * w + x];
    }
  }
  return total;
}

// Tìm độ lệch (dx, dy) của 1 khối lưới so với toạ độ mẫu: dò thô bước 3px rồi tinh ±2px
function findGridOffset(gridDef, outW, outH) {
  const cells = [];
  for (const fx of gridDef.cols) for (const fy of gridDef.rows) cells.push([fx * outW, fy * outH]);
  const range = OMR_TEMPLATE.searchRange;
  let best = { s: -1, dx: 0, dy: 0 };
  for (let dy = -range; dy <= range; dy += 3) {
    for (let dx = -range; dx <= range; dx += 3) {
      const s = ringScore(cells, dx, dy);
      if (s > best.s) best = { s, dx, dy };
    }
  }
  const c = { dx: best.dx, dy: best.dy };
  for (let dy = c.dy - 2; dy <= c.dy + 2; dy++) {
    for (let dx = c.dx - 2; dx <= c.dx + 2; dx++) {
      const s = ringScore(cells, dx, dy);
      if (s > best.s) best = { s, dx, dy };
    }
  }
  return { dx: best.dx, dy: best.dy };
}

// Khối lưới của Phần I (dùng chung đối tượng để giữ độ lệch đã dò)
const PHAN1_LEFT_DEF  = { cols: OMR_TEMPLATE.phan1.colsLeft,  rows: OMR_TEMPLATE.phan1.rows, off: { dx: 0, dy: 0 } };
const PHAN1_RIGHT_DEF = { cols: OMR_TEMPLATE.phan1.colsRight, rows: OMR_TEMPLATE.phan1.rows, off: { dx: 0, dy: 0 } };
OMR_TEMPLATE.sbd.off  = { dx: 0, dy: 0 };
OMR_TEMPLATE.made.off = { dx: 0, dy: 0 };

// Chuẩn bị đọc 1 phiếu: lấy ảnh xám, tự căn lại từng khối lưới (mỗi khối lệch khác nhau vì
// ô vuông góc bị cắt mép/giấy cong), rồi tính mức nền. Gọi 1 lần trước các hàm check*.
function prepareSheet(ctx, outW, outH) {
  buildSheetGray(ctx, outW, outH);
  OMR_TEMPLATE.sbd.off  = findGridOffset(OMR_TEMPLATE.sbd, outW, outH);
  OMR_TEMPLATE.made.off = findGridOffset(OMR_TEMPLATE.made, outW, outH);
  PHAN1_LEFT_DEF.off    = findGridOffset(PHAN1_LEFT_DEF, outW, outH);
  PHAN1_RIGHT_DEF.off   = PHAN1_LEFT_DEF.off; // cột phải không có ô in sẵn để dò -> dùng độ lệch cột trái

  // Mức nền = trung vị độ tối của mọi ô (SBD, Mã đề, cột trái): phần lớn là ô trống
  const all = [];
  [OMR_TEMPLATE.sbd, OMR_TEMPLATE.made, PHAN1_LEFT_DEF].forEach(g => {
    readGridDarkness(null, g, outW, outH).forEach(col => col.forEach(v => all.push(v)));
  });
  all.sort((a, b) => a - b);
  currentBaseline = all[Math.floor(all.length / 2)] || 0;
}

// Đọc độ tối của toàn bộ 1 khối lưới (vd: sbd, made, phan1), đã cộng độ lệch đã dò
// Trả về mảng 2 chiều: darkness[colIndex][rowIndex]
function readGridDarkness(ctx, gridDef, outW, outH) {
  const off = gridDef.off || { dx: 0, dy: 0 };
  const darkness = [];
  for (const fx of gridDef.cols) {
    const colVals = [];
    const px = fx * outW + off.dx;
    for (const fy of gridDef.rows) {
      colVals.push(sampleBubbleDarkness(px, fy * outH + off.dy));
    }
    darkness.push(colVals);
  }
  return darkness;
}

// Xác định trong 1 nhóm ô (vd: 6 ô A-F của 1 câu, hoặc 10 ô digit 0-9 của
// 1 cột SBD) thì ô nào được coi là "đã tô", dựa trên so sánh TƯƠNG ĐỐI:
// ô đậm nhất phải đủ đậm so với mức nền (minOver) VÀ đậm hơn hẳn ô đậm-nhì
// (ratio) thì mới nhận. Trả về index ô được tô, hoặc -1 nếu
// không xác định được (bỏ trống, hoặc 2+ ô đậm ngang nhau).
function pickFilledIndex(vals) {
  let maxV = -1, maxI = -1, secondV = -1;
  vals.forEach((v, i) => {
    if (v > maxV) { secondV = maxV; maxV = v; maxI = i; }
    else if (v > secondV) { secondV = v; }
  });
  const over = maxV - currentBaseline;
  if (over < OMR_TEMPLATE.minOver) return -1;                 // không có ô nào đủ đậm
  if (maxV - secondV < OMR_TEMPLATE.ratio * over) return -1;   // 2+ ô đậm -> bỏ trống
  return maxI;
}

// Kiểm tra khối Số báo danh: mỗi cột (6 cột) phải có ĐÚNG 1 ô được tô.
// Trả về { ok: boolean, sbdString: string|null, errorCols: number[] }
function checkSBDGrid(ctx, outW, outH) {
  const darkness = readGridDarkness(ctx, OMR_TEMPLATE.sbd, outW, outH);
  const errorCols = [];
  let sbdDigits = [];

  darkness.forEach((colVals, colIdx) => {
    const filledRow = pickFilledIndex(colVals);
    if (filledRow === -1) {
      errorCols.push(colIdx + 1); // lưu số thứ tự cột (1-6) cho dễ đọc thông báo
      sbdDigits.push('?');
    } else {
      sbdDigits.push(String(filledRow)); // filledRow chính là chữ số 0-9
    }
  });

  return {
    ok: errorCols.length === 0,
    sbdString: sbdDigits.join(''),
    errorCols,
    darkness
  };
}

// Kiểm tra khối Mã Đề: cấu trúc giống hệt Số báo danh (mỗi cột phải có
// ĐÚNG 1 ô được tô), chỉ khác là có 3 cột thay vì 6.
function checkMadeGrid(ctx, outW, outH) {
  const darkness = readGridDarkness(ctx, OMR_TEMPLATE.made, outW, outH);
  const errorCols = [];
  let digits = [];

  darkness.forEach((colVals, colIdx) => {
    const filledRow = pickFilledIndex(colVals);
    if (filledRow === -1) {
      errorCols.push(colIdx + 1);
      digits.push('?');
    } else {
      digits.push(String(filledRow));
    }
  });

  return {
    ok: errorCols.length === 0,
    madeString: digits.join(''),
    errorCols,
    darkness
  };
}

// Kiểm tra khối Phần I (40 câu trắc nghiệm, 4 đáp án A/B/C/D mỗi câu,
// chia 2 CỘT song song: cột trái = câu 1-20, cột phải = câu 21-40, dùng
// chung danh sách hàng OMR_TEMPLATE.phan1.rows).
// Cũng như bản 20 câu trước đây: mỗi HÀNG (câu hỏi) phải có đúng 1 CỘT
// (đáp án) được tô. KHÔNG chặn upload nếu 1 câu bị bỏ trống hoặc tô nhầm
// 2 đáp án - chỉ để trống ô đó trong bảng kết quả và đánh dấu lại để
// kiểm tra tay, vì học sinh có quyền bỏ trống câu (khác với SBD/Mã Đề
// luôn phải có giá trị).
const ANSWER_LETTERS = ['A', 'B', 'C', 'D'];

// readGridDarkness() gốc nhận (ctx, gridDef, outW, outH) - dùng lại để
// đọc riêng từng cột-nhóm (trái/phải) của Phần I.
function readPhan1Darkness(ctx, outW, outH) {
  const rows = OMR_TEMPLATE.phan1.rows;
  const left  = readGridDarkness(ctx, PHAN1_LEFT_DEF, outW, outH);
  const right = OMR_TEMPLATE.activeQuestions > 20
    ? readGridDarkness(ctx, PHAN1_RIGHT_DEF, outW, outH)
    : null; // phiếu 20 câu: không đọc cột phải (tránh đọc nhầm chữ thành đáp án)
  return { left, right }; // mỗi bên: darkness[colIdx][rowIdx], colIdx 0..3 = A..D
}

function checkPhan1Grid(ctx, outW, outH) {
  const { left, right } = readPhan1Darkness(ctx, outW, outH);
  const numRows = OMR_TEMPLATE.phan1.rows.length; // 20 hàng dùng chung cho mỗi cột
  const answers = [];
  const ambiguousQuestions = []; // số thứ tự câu (1-based, 1..40) bị bỏ trống hoặc tô >1 đáp án

  function readOneQuestion(darkness, rowIdx, questionNumber) {
    const vals = darkness.map(colVals => colVals[rowIdx]);
    const filledCol = pickFilledIndex(vals);
    if (filledCol === -1) {
      answers.push('');
      ambiguousQuestions.push(questionNumber);
    } else {
      answers.push(ANSWER_LETTERS[filledCol]);
    }
  }

  // Cột trái: câu 1-20
  for (let rowIdx = 0; rowIdx < numRows; rowIdx++) {
    readOneQuestion(left, rowIdx, rowIdx + 1);
  }
  // Cột phải: câu 21-40 (chỉ đọc khi phiếu thật sự có; còn lại để trống cho đủ 40 phần tử)
  for (let rowIdx = 0; rowIdx < numRows; rowIdx++) {
    if (right) {
      readOneQuestion(right, rowIdx, rowIdx + 21);
    } else {
      answers.push('');
    }
  }

  return { answers, ambiguousQuestions, darkness: { left, right } };
}

// ============================================================
// DEBUG: vẽ chấm màu tại từng điểm lấy mẫu để kiểm tra toạ độ có
// đúng tâm ô tròn không (chỉ hiển thị trên preview, KHÔNG upload)
// Bật/tắt bằng biến DEBUG_OMR bên dưới.
// ============================================================
const DEBUG_OMR = false; // bật true khi cần gỡ lỗi (tạo canvas lớn mỗi lần quét nên làm máy chậm dần)

function drawDebugOverlay(sourceCanvas, gridDef, outW, outH, darkness) {
  const debugCanvas = document.createElement('canvas');
  debugCanvas.width = outW;
  debugCanvas.height = outH;
  const dctx = debugCanvas.getContext('2d');
  dctx.drawImage(sourceCanvas, 0, 0);

  const radius = Math.max(3, Math.round(outW * OMR_TEMPLATE.bubbleRadiusFrac));

  gridDef.cols.forEach((fx, colIdx) => {
    const px = fx * outW + ((gridDef.off && gridDef.off.dx) || 0);
    const winRow = pickFilledIndex(darkness[colIdx]);
    gridDef.rows.forEach((fy, rowIdx) => {
      const py = fy * outH + ((gridDef.off && gridDef.off.dy) || 0);
      const d = darkness[colIdx][rowIdx];
      const filled = rowIdx === winRow;
      dctx.beginPath();
      dctx.arc(px, py, radius, 0, Math.PI * 2);
      dctx.strokeStyle = filled ? '#00ff00' : '#ff0000';
      dctx.lineWidth = 2;
      dctx.stroke();
      // Ghi giá trị độ đậm (0-255) nhỏ bên cạnh để đọc số cụ thể
      dctx.fillStyle = filled ? '#00ff00' : '#ff0000';
      dctx.font = '9px sans-serif';
      dctx.fillText(Math.round(d), px + radius + 1, py + 3);
    });
  });

  return debugCanvas;
}


function showPreviewAndUpload(sbdCheck, madeCheck, phan1Check) {
  const dataUrl = resultCanvas.toDataURL('image/jpeg', 0.92); // ảnh SẠCH để upload
  previewBox.classList.remove('hidden');

  if (DEBUG_OMR && sbdCheck && sbdCheck.darkness) {
    // Hiển thị bản có chấm debug (không ảnh hưởng ảnh upload lên Drive)
    const debugCanvas = drawDebugOverlay(resultCanvas, OMR_TEMPLATE.sbd, OUT_W, OUT_H, sbdCheck.darkness);
    previewImg.src = debugCanvas.toDataURL('image/jpeg', 0.92);
  } else {
    previewImg.src = dataUrl;
  }

  if (sbdCheck && !sbdCheck.ok) {
    // Số báo danh tô sai (thiếu hoặc thừa ô trong 1 cột nào đó)
    // -> KHÔNG upload lên Google Drive, chỉ cảnh báo và chờ người dùng xử lý
    uploadStatusEl.textContent =
      '⚠ Số báo danh tô sai ở cột: ' + sbdCheck.errorCols.join(', ') +
      ' (mỗi cột phải tô đúng 1 ô). Ảnh này CHƯA được lưu lên Drive — ' +
      'hãy kiểm tra lại phiếu giấy rồi bấm "Chụp lại".';
    uploadStatusEl.className = 'upload-status error';
    feedbackWarning(); // "Tè tè" + rung cảnh báo
    return; // dừng lại đây, không gọi uploadToDrive
  }

  if (madeCheck && !madeCheck.ok) {
    // Mã Đề tô sai (thiếu hoặc thừa ô trong 1 cột nào đó) -> cũng chặn lại,
    // vì thiếu Mã Đề sẽ không biết dùng đáp án đúng nào để chấm sau này.
    uploadStatusEl.textContent =
      '⚠ Mã Đề tô sai ở cột: ' + madeCheck.errorCols.join(', ') +
      ' (mỗi cột phải tô đúng 1 ô). Ảnh này CHƯA được lưu lên Drive — ' +
      'hãy kiểm tra lại phiếu giấy rồi bấm "Chụp lại".';
    uploadStatusEl.className = 'upload-status error';
    feedbackWarning();
    return;
  }

  // Gói lại toàn bộ dữ liệu đã đọc được để gửi kèm ảnh lên Apps Script,
  // Apps Script sẽ ghi thẳng vào Google Sheet, khớp dòng theo SBD.
  const reading = {
    sbd: sbdCheck.sbdString,
    made: madeCheck.madeString,
    answers: phan1Check.answers,               // mảng 40 phần tử: 'A'/'B'/'C'/'D' hoặc '' nếu bỏ trống/tô nhầm
    ambiguousQuestions: phan1Check.ambiguousQuestions // câu cần người chấm kiểm tra tay
  };

  // Việc kiểm tra SBD trùng do server (Apps Script) đảm nhiệm - xem uploadToDrive().

  finalizeUpload(dataUrl, sbdCheck, reading);
}

// Hiện hộp thoại tự vẽ hỏi xác nhận SBD trùng (thay cho confirm() của
// trình duyệt). onOverwrite/onCancel là callback ứng với 2 nút bấm.
function showDuplicateModal(sbdString, onOverwrite, onCancel) {
  dupMessageEl.textContent = 'Số báo danh này đã trùng';
  dupCancelBtn.textContent = 'Hủy';
  dupOverwriteBtn.textContent = 'Ghi đè';
  dupModal.classList.remove('hidden');

  function cleanup() {
    dupModal.classList.add('hidden');
    dupOverwriteBtn.removeEventListener('click', handleOverwrite);
    dupCancelBtn.removeEventListener('click', handleCancel);
  }
  function handleOverwrite() { cleanup(); onOverwrite(); }
  function handleCancel() { cleanup(); onCancel(); }

  dupOverwriteBtn.addEventListener('click', handleOverwrite);
  dupCancelBtn.addEventListener('click', handleCancel);
}

// Hoàn tất: phát "Tít" thành công, đánh dấu SBD đã quét, rồi upload lên Drive/Sheet.
function finalizeUpload(dataUrl, sbdCheck, reading) {
  // Quét/nhận diện thành công ngay tại đây -> phát "Tít" NGAY LẬP TỨC,
  // không chờ upload lên Google Drive xong mới kêu
  uploadStatusEl.textContent = 'Đang tải lên Google Drive...';
  uploadStatusEl.className = 'upload-status';
  feedbackSuccess(); // "Tít" + rung nhẹ báo thành công
  scannedSBDs.add(sbdCheck.sbdString); // ghi nhận SBD này đã quét trong phiên

  uploadToDrive(dataUrl, reading);
}

async function uploadToDrive(dataUrl, reading, overwrite = false) {
  const base64 = dataUrl.split(',')[1];
  const filename = (reading && reading.sbd ? reading.sbd : 'phieu_' + Date.now()) + '.jpg'; // tên ảnh = SBD (vd: 001112.jpg)

  try {
    const res = await fetch(WEBAPP_URL, {
      method: 'POST',
      // Dùng text/plain để tránh trình duyệt gửi preflight OPTIONS
      // (Apps Script Web App không xử lý OPTIONS mặc định)
      headers: { 'Content-Type': 'text/plain;charset=utf-8' },
      body: JSON.stringify({ filename, mimeType: 'image/jpeg', data: base64, reading, overwrite })
    });

    const result = await res.json();
    if (result && result.success) {
      if (result.duplicate) {
        // Server báo SBD này đã có (dữ liệu trên Sheet hoặc ảnh trong Drive).
        // Server CHƯA lưu gì cả -> hỏi người dùng: Hủy hay Ghi đè.
        feedbackWarning();
        showDuplicateModal(
          reading.sbd,
          () => { // Ghi đè: gửi lại kèm overwrite=true -> server xoá dữ liệu + ảnh cũ rồi lưu mới
            uploadStatusEl.textContent = 'Đang ghi đè...';
            uploadStatusEl.className = 'upload-status';
            feedbackSuccess();
            uploadToDrive(dataUrl, reading, true);
          },
          () => { // Hủy: coi như chưa chụp gì, dữ liệu cũ giữ nguyên
            previewBox.classList.add('hidden');
            history = [];
            lockedUntil = Date.now() + CAPTURE_COOLDOWN;
            setStatus('Đưa phiếu vào khung hình', false);
          }
        );
        return;
      }
      uploadStatusEl.textContent = '✔ Đã lưu vào Google Drive';
      uploadStatusEl.className = 'upload-status success';
      // (Âm thanh "Tít" đã phát ngay lúc quét xong ở showPreviewAndUpload(),
      // không phát lại ở đây để tránh chờ mạng)

      // Tự động quay lại chế độ quét ngay sau khi lưu thành công,
      // để chụp phiếu tiếp theo mà không cần bấm "Chụp lại"
      setTimeout(() => {
        previewImg.removeAttribute('src');
        previewBox.classList.add('hidden');
        history = [];
        lockedUntil = 0;
        setStatus('Đưa phiếu vào khung hình', false);
      }, 400); // để 0.4s cho kịp thấy dấu ✔ rồi quay lại ngay
    } else {
      throw new Error((result && result.error) || 'Không rõ lỗi');
    }
  } catch (err) {
    uploadStatusEl.textContent = '✖ Lỗi tải lên: ' + err.message;
    uploadStatusEl.className = 'upload-status error';
  }
}

// ---------- Khởi động ----------
startCamera();
