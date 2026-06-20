/* ===================================================================
   Stone Layout Designer — Slabsmith 風格石材排版 (v2)
   多邊形零件 · 邊線接合(miter) · 2D 平移/縮放/磁吸 · 用料率 · 存讀檔
   左：平面/材質 nesting   右：3D 組裝 + 即時 UV 貼圖
   =================================================================== */
'use strict';

/* ---------------- 全域狀態 ---------------- */
const State = {
  slabs: [],          // {id,name,img,src,widthIn,heightIn,originX,originY,tex}
  parts: [],          // 見 makePart()
  selectedId: null,
  nextId: 1,
  view2d: { scale: 2, offX: 0, offY: 0, fitted: false },
  snapOn: false,
  gridIn: 6,          // 磁吸格 (in)
  snapGapIn: 0.5,
  // 模式
  drawMode: null,     // {pts:[...], cursor, penDrag}
  nodeEdit: null,     // 進入節點編輯的零件 id
  gizmoMode: null,    // 'move' | 'rotate'：3D 操作 gizmo
  standPick: false,   // 選底邊立起：等待點選一條邊
  placeMode: null,    // 'rect' | 'tri'：拖曳建立中
  placeDrag: null,    // {x0,y0,x1,y1} 世界座標(in)
  edgeOrient: null,   // {stage:'src'|'dst', src:{partId,edge}}
};

const SLAB_GAP = 6;
const TRAY_GAP = 14;
const EDGE_COLOR = 0x6b6f78;
const D2R = Math.PI / 180;
const IN2CM = 2.54;                                   // 顯示用公分；內部一律英吋
const cm = (inch) => Math.round((inch || 0) * IN2CM * 100) / 100;
const inFromCm = (c) => (+c || 0) / IN2CM;
const SQIN2M2 = 1 / 1550.0031;                        // 1 in² = ? m²

/* ---------------- DOM ---------------- */
const $ = (id) => document.getElementById(id);
const canvas2d = $('canvas2d');
const ctx = canvas2d.getContext('2d');
function setStatus(t) { $('status').textContent = t; }

/* ===================================================================
   3D 場景
   =================================================================== */
let renderer, scene, camera, controls, raycaster, ground, grid3d;
const BG = { dark: 0x0d0e11, light: 0xeef1f5 };

function init3D() {
  const wrap = $('canvasWrap3d');
  renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setPixelRatio(window.devicePixelRatio || 1);
  renderer.setSize(wrap.clientWidth, wrap.clientHeight);
  renderer.shadowMap.enabled = true;
  wrap.appendChild(renderer.domElement);

  scene = new THREE.Scene();
  scene.background = new THREE.Color(BG.dark);

  camera = new THREE.PerspectiveCamera(45, wrap.clientWidth / wrap.clientHeight, 0.5, 5000);
  camera.position.set(60, 70, 90);

  controls = new THREE.OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true;
  controls.dampingFactor = 0.08;

  scene.add(new THREE.AmbientLight(0xffffff, 0.6));
  const dir = new THREE.DirectionalLight(0xffffff, 0.85);
  dir.position.set(80, 140, 60);
  dir.castShadow = true;
  dir.shadow.mapSize.set(1024, 1024);
  Object.assign(dir.shadow.camera, { left: -200, right: 200, top: 200, bottom: -200 });
  scene.add(dir);

  grid3d = new THREE.GridHelper(400, 40, 0x3a3f4a, 0x23262d);
  scene.add(grid3d);
  ground = new THREE.Mesh(new THREE.PlaneGeometry(4000, 4000), new THREE.ShadowMaterial({ opacity: 0.25 }));
  ground.rotation.x = -Math.PI / 2;
  ground.receiveShadow = true;
  scene.add(ground);

  raycaster = new THREE.Raycaster();
  buildGizmo();
  buildMoveGizmo();
  setup3DPointer();
  animate();
  window.addEventListener('resize', onResize);
}

function setBackground(mode) {
  scene.background.set(mode === 'light' ? BG.light : BG.dark);
  if (mode === 'light') grid3d.material.color && grid3d.material.color.set(0xcfd4db);
  // GridHelper 用兩種顏色，重建較簡單
  scene.remove(grid3d);
  grid3d = new THREE.GridHelper(400, 40,
    mode === 'light' ? 0x9aa1ad : 0x3a3f4a,
    mode === 'light' ? 0xc9ced6 : 0x23262d);
  scene.add(grid3d);
  $('bgDarkBtn').classList.toggle('active', mode !== 'light');
  $('bgLightBtn').classList.toggle('active', mode === 'light');
}

function onResize() {
  const wrap = $('canvasWrap3d');
  camera.aspect = wrap.clientWidth / wrap.clientHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(wrap.clientWidth, wrap.clientHeight);
  draw2D();
}
function animate() {
  requestAnimationFrame(animate);
  controls.update();
  updateGizmo();
  renderer.render(scene, camera);
}

/* ===================================================================
   零件 (多邊形模型)
   verts: [{x,y}] 本地座標(in)，最小角在 (0,0)
   =================================================================== */
// 每個頂點(節點)帶兩支貝茲控制桿(相對偏移)：
//   hox,hoy = 出向控制桿(往下一節點方向)；hix,hiy = 入向控制桿(往上一節點方向)
//   平滑節點：hix=-hox, hiy=-hoy；角點：兩者皆 0 → 直線
function mkV(x, y) { return { x, y, hox: 0, hoy: 0, hix: 0, hiy: 0 }; }
function rectVerts(w, d) { return [mkV(0, 0), mkV(w, 0), mkV(w, d), mkV(0, d)]; }
function triVerts(w, d) { return [mkV(0, d), mkV(w, d), mkV(0, 0)]; }

// 邊 i (verts[i]→verts[i+1]) 的三次貝茲四點(本地座標)
function edgeBezier(verts, i) {
  const a = verts[i], b = verts[(i + 1) % verts.length];
  const p0 = { x: a.x, y: a.y };
  const p1 = { x: a.x + (a.hox || 0), y: a.y + (a.hoy || 0) };
  const p2 = { x: b.x + (b.hix || 0), y: b.y + (b.hiy || 0) };
  const p3 = { x: b.x, y: b.y };
  const curved = !!((a.hox || a.hoy || b.hix || b.hiy));
  return { p0, p1, p2, p3, curved };
}
function cubicPt(e, u) {
  const iu = 1 - u, a = iu * iu * iu, c = 3 * iu * iu * u, d = 3 * iu * u * u, f = u * u * u;
  return { x: a * e.p0.x + c * e.p1.x + d * e.p2.x + f * e.p3.x, y: a * e.p0.y + c * e.p1.y + d * e.p2.y + f * e.p3.y };
}
// 攤平成折線(本地座標)，供面積/碰撞/外框使用
function flattenLocal(verts, seg = 24) {
  const out = [];
  for (let i = 0; i < verts.length; i++) {
    const e = edgeBezier(verts, i);
    out.push({ x: e.p0.x, y: e.p0.y });
    if (e.curved) for (let t = 1; t < seg; t++) out.push(cubicPt(e, t / seg));
  }
  return out;
}

function makePart(opts = {}) {
  const id = State.nextId++;
  const idx = State.parts.length;
  const verts = opts.verts || rectVerts(opts.widthIn ?? 24, opts.depthIn ?? 24);
  const part = {
    id,
    name: opts.name || `零件 ${id}`,
    verts,
    thickIn: opts.thickIn ?? 1.25,
    elevIn: opts.elevIn ?? 0,
    vertical: opts.vertical ?? false,
    rot2d: opts.rot2d ?? 0,             // 平面旋轉(度)
    slabId: null,
    layoutX: opts.layoutX ?? 0,
    layoutY: opts.layoutY ?? 0,
    pos3d: opts.pos3d || { x: (idx % 4) * 40 - 60, z: Math.floor(idx / 4) * 40 - 20 },
    rotY: opts.rotY ?? 0,                // 3D 偏航(繞垂直 Y)
    tiltX: opts.tiltX ?? 0,             // 3D 前後傾(繞 X)
    tiltZ: opts.tiltZ ?? 0,             // 3D 左右傾(繞 Z)
    group: null, body: null, topSkin: null, botSkin: null, outline: null,
  };
  if (opts.layoutX === undefined) placeInTray(part, idx);
  State.parts.push(part);
  buildPartMesh(part);
  rebuild2DLayout();
  if (opts.select !== false) selectPart(id);
  return part;
}

function placeInTray(part, idx) {
  const trayY = traySafeY();
  part.slabId = null;
  part.layoutX = (idx % 5) * 30;
  part.layoutY = trayY + Math.floor(idx / 5) * 30;
}
function traySafeY() {
  let y = 0;
  for (const s of State.slabs) y = Math.max(y, s.originY + s.heightIn);
  return y + TRAY_GAP;
}

/* ---------- 幾何輔助 ---------- */
function bbox(part) {
  const pts = flattenLocal(part.verts);
  let minx = Infinity, miny = Infinity, maxx = -Infinity, maxy = -Infinity;
  for (const v of pts) {
    minx = Math.min(minx, v.x); miny = Math.min(miny, v.y);
    maxx = Math.max(maxx, v.x); maxy = Math.max(maxy, v.y);
  }
  return { minx, miny, maxx, maxy, w: maxx - minx, h: maxy - miny, cx: (minx + maxx) / 2, cy: (miny + maxy) / 2 };
}
function polyArea(verts) {
  const pts = flattenLocal(verts);
  let a = 0;
  for (let i = 0; i < pts.length; i++) {
    const p = pts[i], q = pts[(i + 1) % pts.length];
    a += p.x * q.y - q.x * p.y;
  }
  return Math.abs(a) / 2;
}
// nesting：本地點 → 2D 世界座標(in)
function nestPoint(part, lx, ly) {
  const a = part.rot2d * D2R, c = Math.cos(a), s = Math.sin(a);
  return { x: part.layoutX + lx * c - ly * s, y: part.layoutY + lx * s + ly * c };
}
// 反向：2D 世界座標 → 本地點
function invNest(part, wx, wy) {
  const a = part.rot2d * D2R, c = Math.cos(a), s = Math.sin(a);
  const dx = wx - part.layoutX, dy = wy - part.layoutY;
  return { x: dx * c + dy * s, y: -dx * s + dy * c };
}
function pointInPoly(px, py, pts) {
  let inside = false;
  for (let i = 0, j = pts.length - 1; i < pts.length; j = i++) {
    const xi = pts[i].x, yi = pts[i].y, xj = pts[j].x, yj = pts[j].y;
    if (((yi > py) !== (yj > py)) && (px < (xj - xi) * (py - yi) / (yj - yi) + xi)) inside = !inside;
  }
  return inside;
}

/* ---------- 3D mesh ---------- */
function buildPartMesh(part) {
  if (part.group) { scene.remove(part.group); disposeGroup(part.group); }
  const bb = bbox(part);
  // 置中後的 shape（支援弧形邊）
  const shape = new THREE.Shape();
  shape.moveTo(part.verts[0].x - bb.cx, part.verts[0].y - bb.cy);
  for (let i = 0; i < part.verts.length; i++) {
    const e = edgeBezier(part.verts, i);
    if (e.curved) shape.bezierCurveTo(e.p1.x - bb.cx, e.p1.y - bb.cy, e.p2.x - bb.cx, e.p2.y - bb.cy, e.p3.x - bb.cx, e.p3.y - bb.cy);
    else shape.lineTo(e.p3.x - bb.cx, e.p3.y - bb.cy);
  }
  shape.closePath();

  const t = part.thickIn;
  const bodyGeo = new THREE.ExtrudeGeometry(shape, { depth: t, bevelEnabled: false, curveSegments: 24 });
  bodyGeo.translate(0, 0, -t / 2);
  const bodyMat = new THREE.MeshStandardMaterial({ color: 0xc9a17a, roughness: 0.85 });
  const body = new THREE.Mesh(bodyGeo, bodyMat);
  body.castShadow = true; body.receiveShadow = true;

  const skinMat = () => new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: 0.6, side: THREE.DoubleSide });
  const topGeo = new THREE.ShapeGeometry(shape, 24);
  const top = new THREE.Mesh(topGeo, skinMat()); top.position.z = t / 2 + 0.02; top.visible = false;
  // 底面用相同外形(不旋轉，避免非對稱形狀被鏡像)，靠 DoubleSide 從背面也能看到
  const botGeo = new THREE.ShapeGeometry(shape, 24);
  const bot = new THREE.Mesh(botGeo, skinMat()); bot.position.z = -t / 2 - 0.02; bot.visible = false;

  const inner = new THREE.Group();
  inner.add(body); inner.add(top); inner.add(bot);

  const group = new THREE.Group();
  group.add(inner);
  group.userData.partId = part.id;
  body.userData.partId = part.id; top.userData.partId = part.id; bot.userData.partId = part.id;

  // 選取外框
  const eg = new THREE.EdgesGeometry(bodyGeo);
  const outline = new THREE.LineSegments(eg, new THREE.LineBasicMaterial({ color: 0x4ea1ff }));
  outline.visible = false; body.add(outline);

  part.group = group; part.inner = inner; part.body = body;
  part.topSkin = top; part.botSkin = bot; part.outline = outline;
  scene.add(group);

  applyPartTexture(part);
  updatePartTransform(part);
}

function disposeGroup(g) {
  g.traverse(o => {
    if (o.geometry) o.geometry.dispose();
    if (o.material) (Array.isArray(o.material) ? o.material : [o.material]).forEach(m => m.dispose());
  });
}

function updatePartTransform(part) {
  const bb = bbox(part);
  part.inner.rotation.set(part.vertical ? 0 : -Math.PI / 2, 0, 0);
  part.group.rotation.set(part.tiltX || 0, part.rotY || 0, part.tiltZ || 0);
  const yc = part.vertical ? (part.elevIn + bb.h / 2) : (part.elevIn + part.thickIn / 2);
  part.group.position.set(part.pos3d.x, yc, part.pos3d.z);
  part.group.updateMatrixWorld(true);
}

/* ---------- 即時貼圖：UV 對應石材 ---------- */
function getSlabTex(slab) {
  if (!slab.tex && slab.img) {
    slab.tex = new THREE.Texture(slab.img);
    slab.tex.colorSpace = THREE.SRGBColorSpace || slab.tex.colorSpace;
    slab.tex.needsUpdate = true;
  }
  return slab.tex;
}

function applyPartTexture(part) {
  const slab = State.slabs.find(s => s.id === part.slabId);
  const top = part.topSkin, bot = part.botSkin;
  if (!slab || !slab.img) {
    top.visible = false; bot.visible = false;
    part.body.material.color.set(0xc9a17a);
    return;
  }
  const tex = getSlabTex(slab);
  top.material.map = tex; bot.material.map = tex;
  top.material.color.set(0xffffff); bot.material.color.set(0xffffff);
  top.visible = true; bot.visible = true;
  part.body.material.color.set(0x8a8f98);
  setSkinUV(part, top); setSkinUV(part, bot);
  top.material.needsUpdate = bot.material.needsUpdate = true;
}

function setSkinUV(part, skin) {
  const slab = State.slabs.find(s => s.id === part.slabId);
  if (!slab) return;
  const bb = bbox(part);
  const pos = skin.geometry.attributes.position;
  const uv = skin.geometry.attributes.uv;
  for (let i = 0; i < pos.count; i++) {
    // 置中本地 → 原始本地
    const lx = pos.getX(i) + bb.cx;
    const ly = pos.getY(i) + bb.cy;
    const w = nestPoint(part, lx, ly);
    const u = (w.x - slab.originX) / slab.widthIn;
    const v = 1 - (w.y - slab.originY) / slab.heightIn;
    uv.setXY(i, u, v);
  }
  uv.needsUpdate = true;
}

/* ===================================================================
   2D 排版畫布
   =================================================================== */
function rebuild2DLayout() {
  let y = 0;
  for (const s of State.slabs) { s.originX = 0; s.originY = y; y += s.heightIn + SLAB_GAP; }
  if (!State.view2d.fitted) fitView2D();
  draw2D();
  updateStats();
}

function fitView2D() {
  resizeBacking();
  const W = canvas2d.width, H = canvas2d.height;
  let maxX = 80, maxY = 80;
  for (const s of State.slabs) { maxX = Math.max(maxX, s.originX + s.widthIn); maxY = Math.max(maxY, s.originY + s.heightIn); }
  for (const p of State.parts) { const bb = bbox(p); maxX = Math.max(maxX, p.layoutX + bb.maxx); maxY = Math.max(maxY, p.layoutY + bb.maxy); }
  maxX += 10; maxY += 14;
  const pad = 20;
  const scale = Math.min((W - pad * 2) / maxX, (H - pad * 2) / maxY);
  State.view2d.scale = scale;
  State.view2d.offX = pad + (W - pad * 2 - maxX * scale) / 2;
  State.view2d.offY = pad + (H - pad * 2 - maxY * scale) / 2;
  State.view2d.fitted = true;
}

function w2s(x, y) { const v = State.view2d; return [x * v.scale + v.offX, y * v.scale + v.offY]; }
function s2w(px, py) { const v = State.view2d; return [(px - v.offX) / v.scale, (py - v.offY) / v.scale]; }

function resizeBacking() {
  const wrap = $('canvasWrap2d');
  if (canvas2d.width !== wrap.clientWidth || canvas2d.height !== wrap.clientHeight) {
    canvas2d.width = wrap.clientWidth; canvas2d.height = wrap.clientHeight;
  }
}

function draw2D() {
  resizeBacking();
  const W = canvas2d.width, H = canvas2d.height;
  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = '#0a0b0d'; ctx.fillRect(0, 0, W, H);

  if (State.snapOn) drawGrid();

  for (const s of State.slabs) {
    const [x, y] = w2s(s.originX, s.originY);
    const w = s.widthIn * State.view2d.scale, h = s.heightIn * State.view2d.scale;
    if (s.img) ctx.drawImage(s.img, x, y, w, h);
    else { ctx.fillStyle = '#333'; ctx.fillRect(x, y, w, h); }
    ctx.strokeStyle = '#7a8290'; ctx.lineWidth = 1.5; ctx.strokeRect(x, y, w, h);
    ctx.fillStyle = 'rgba(0,0,0,.55)'; ctx.fillRect(x, y, 168, 18);
    ctx.fillStyle = '#cfd3da'; ctx.font = '11px Segoe UI';
    ctx.fillText(`${s.name}  ${cm(s.widthIn)}×${cm(s.heightIn)} cm`, x + 5, y + 13);
  }

  const trayY = traySafeY();
  const [, ty] = w2s(0, trayY - TRAY_GAP / 2);
  ctx.fillStyle = '#5a616e'; ctx.font = '11px Segoe UI';
  ctx.fillText('▼ 待排零件 (拖到上方石材以指定紋理)', 24, ty);

  for (const p of State.parts) drawPart2D(p);
  if (State.drawMode) drawPolyPreview();
  if (State.placeMode && State.placeDrag) drawPlacePreview();
}

function drawGrid() {
  const g = State.gridIn, v = State.view2d;
  const [x0, y0] = s2w(0, 0), [x1, y1] = s2w(canvas2d.width, canvas2d.height);
  ctx.strokeStyle = 'rgba(120,130,150,.12)'; ctx.lineWidth = 1;
  ctx.beginPath();
  for (let x = Math.floor(x0 / g) * g; x < x1; x += g) { const [sx] = w2s(x, 0); ctx.moveTo(sx, 0); ctx.lineTo(sx, canvas2d.height); }
  for (let y = Math.floor(y0 / g) * g; y < y1; y += g) { const [, sy] = w2s(0, y); ctx.moveTo(0, sy); ctx.lineTo(canvas2d.width, sy); }
  ctx.stroke();
}

// 本地點 → 螢幕
function localToScreen(p, lx, ly) { const w = nestPoint(p, lx, ly); return w2s(w.x, w.y); }

function tracePartPath(p) {
  ctx.beginPath();
  const [sx0, sy0] = localToScreen(p, p.verts[0].x, p.verts[0].y);
  ctx.moveTo(sx0, sy0);
  for (let i = 0; i < p.verts.length; i++) {
    const e = edgeBezier(p.verts, i);
    const [x3, y3] = localToScreen(p, e.p3.x, e.p3.y);
    if (e.curved) {
      const [c1x, c1y] = localToScreen(p, e.p1.x, e.p1.y);
      const [c2x, c2y] = localToScreen(p, e.p2.x, e.p2.y);
      ctx.bezierCurveTo(c1x, c1y, c2x, c2y, x3, y3);
    } else ctx.lineTo(x3, y3);
  }
  ctx.closePath();
}

function drawPart2D(p) {
  const sel = p.id === State.selectedId;
  const onSlab = !!p.slabId;
  tracePartPath(p);
  ctx.fillStyle = onSlab ? 'rgba(255,160,80,0.26)' : 'rgba(120,160,255,0.30)';
  ctx.fill();
  ctx.lineWidth = sel ? 2.5 : 1.5;
  ctx.strokeStyle = sel ? '#ffb347' : (onSlab ? '#ff9a4d' : '#7fa8ff');
  ctx.stroke();

  const bb = bbox(p);
  const c = nestPoint(p, bb.cx, bb.miny);
  const [lx, ly] = w2s(c.x, c.y);
  ctx.fillStyle = sel ? '#ffd9a0' : '#e6e8ec'; ctx.font = '11px Segoe UI';
  ctx.fillText(`${p.name}`, lx - 18, ly + 13);

  // 控點
  if (sel && !State.drawMode) {
    if (State.nodeEdit === p.id) drawNodeHandles(p);
    else {
      // 縮放控點：藍色方塊（4 角 + 4 邊中）
      for (const h of resizeHandles(p)) {
        const [hx, hy] = localToScreen(p, h.x, h.y);
        ctx.fillStyle = '#4ea1ff'; ctx.strokeStyle = '#0a0b0d'; ctx.lineWidth = 1;
        ctx.beginPath(); ctx.rect(hx - 4.5, hy - 4.5, 9, 9); ctx.fill(); ctx.stroke();
      }
    }
  }
}

// 節點編輯：畫節點(方塊) + 貝茲控制桿(連線+圓點)
function drawNodeHandles(p) {
  for (let i = 0; i < p.verts.length; i++) {
    const v = p.verts[i];
    const [ax, ay] = localToScreen(p, v.x, v.y);
    // 控制桿連線 + 端點
    const hasOut = v.hox || v.hoy, hasIn = v.hix || v.hiy;
    ctx.strokeStyle = 'rgba(120,200,255,.8)'; ctx.lineWidth = 1;
    if (hasOut) {
      const [ox, oy] = localToScreen(p, v.x + v.hox, v.y + v.hoy);
      ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(ox, oy); ctx.stroke();
      ctx.fillStyle = '#34c3ff'; ctx.beginPath(); ctx.arc(ox, oy, 4.5, 0, 7); ctx.fill();
    }
    if (hasIn) {
      const [ix, iy] = localToScreen(p, v.x + v.hix, v.y + v.hiy);
      ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(ix, iy); ctx.stroke();
      ctx.fillStyle = '#34c3ff'; ctx.beginPath(); ctx.arc(ix, iy, 4.5, 0, 7); ctx.fill();
    }
    // 節點方塊
    ctx.fillStyle = '#ffb347'; ctx.strokeStyle = '#0a0b0d'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.rect(ax - 4.5, ay - 4.5, 9, 9); ctx.fill(); ctx.stroke();
  }
}

function drawPolyPreview() {
  const dm = State.drawMode, pts = dm.pts;
  if (!pts.length) return;
  // 已放置節點之間的三次貝茲
  ctx.strokeStyle = '#4ea1ff'; ctx.lineWidth = 2;
  ctx.beginPath();
  const [s0x, s0y] = w2s(pts[0].x, pts[0].y); ctx.moveTo(s0x, s0y);
  for (let i = 0; i < pts.length - 1; i++) {
    const a = pts[i], b = pts[i + 1];
    const [x3, y3] = w2s(b.x, b.y);
    if (a.hox || a.hoy || b.hix || b.hiy) {
      const [c1x, c1y] = w2s(a.x + a.hox, a.y + a.hoy);
      const [c2x, c2y] = w2s(b.x + b.hix, b.y + b.hiy);
      ctx.bezierCurveTo(c1x, c1y, c2x, c2y, x3, y3);
    } else ctx.lineTo(x3, y3);
  }
  ctx.stroke();
  // 到游標的虛線預覽
  if (dm.cursor && !dm.penDrag) {
    const last = pts[pts.length - 1];
    const [lx, ly] = w2s(last.x, last.y), [cx, cy] = w2s(dm.cursor.x, dm.cursor.y);
    ctx.save(); ctx.setLineDash([5, 4]); ctx.strokeStyle = 'rgba(120,160,255,.6)';
    ctx.beginPath(); ctx.moveTo(lx, ly); ctx.lineTo(cx, cy); ctx.stroke(); ctx.restore();
  }
  // 控制桿
  pts.forEach(v => {
    const [ax, ay] = w2s(v.x, v.y);
    ctx.strokeStyle = 'rgba(120,200,255,.8)'; ctx.fillStyle = '#34c3ff';
    [['hox', 'hoy'], ['hix', 'hiy']].forEach(([hx, hy]) => {
      if (v[hx] || v[hy]) {
        const [ex, ey] = w2s(v.x + v[hx], v.y + v[hy]);
        ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(ex, ey); ctx.stroke();
        ctx.beginPath(); ctx.arc(ex, ey, 4, 0, 7); ctx.fill();
      }
    });
  });
  // 節點
  pts.forEach((v, i) => {
    const [sx, sy] = w2s(v.x, v.y);
    ctx.fillStyle = (i === 0) ? '#ffb347' : '#4ea1ff';
    ctx.beginPath(); ctx.arc(sx, sy, i === 0 ? 5 : 3.5, 0, 7); ctx.fill();
  });
  if (pts.length >= 3) {
    const [sx, sy] = w2s(pts[0].x, pts[0].y);
    ctx.strokeStyle = '#ffb347'; ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.arc(sx, sy, 9, 0, 7); ctx.stroke();
  }
}
function updateDrawInfo() {
  if (!State.drawMode) return;
  $('drawInfo').textContent = `繪製中：${State.drawMode.pts.length} 點（點＝角點、拖曳＝弧線；點回起點閉合）`;
}

/* ---------- 統計 ---------- */
function updateStats() {
  const bar = $('statsBar');
  if (!State.slabs.length) { bar.textContent = '用料率：尚未匯入石材'; return; }
  const parts = [];
  for (const s of State.slabs) {
    const used = State.parts.filter(p => p.slabId === s.id).reduce((a, p) => a + polyArea(p.verts), 0);
    const total = s.widthIn * s.heightIn;
    const pct = total ? (used / total * 100) : 0;
    parts.push(`${s.name}: ${(used * SQIN2M2).toFixed(2)}/${(total * SQIN2M2).toFixed(2)} m² (${pct.toFixed(0)}%)`);
  }
  const tray = State.parts.filter(p => !p.slabId).length;
  bar.textContent = `用料率 ▸ ${parts.join('   ·   ')}   ·   待排 ${tray} 件`;
}

/* ---------- 2D 互動：拖曳 / 平移 / 縮放 / 繪製 ---------- */
let drag2d = null, pan2d = null, dragResize = null, dragNode = null;
function snap(v) { return State.snapOn ? Math.round(v / State.gridIn) * State.gridIn : v; }

canvas2d.addEventListener('pointerdown', (e) => {
  const rect = canvas2d.getBoundingClientRect();
  const px = e.clientX - rect.left, py = e.clientY - rect.top;
  const [wx, wy] = s2w(px, py);

  if (State.drawMode) {
    const dm = State.drawMode;
    // 點回起點 → 閉合
    if (dm.pts.length >= 3) {
      const [fx, fy] = w2s(dm.pts[0].x, dm.pts[0].y);
      if (Math.hypot(px - fx, py - fy) <= 10) { finishPolygon(); return; }
    }
    const v = mkV(snap(wx), snap(wy));
    dm.pts.push(v);
    dm.penDrag = { v, ax: snap(wx), ay: snap(wy) };   // 按住拖曳 → 拉出控制桿(平滑點)
    canvas2d.setPointerCapture(e.pointerId);
    updateDrawInfo(); draw2D();
    return;
  }

  // 拖曳建立矩形/三角
  if (State.placeMode) {
    State.placeDrag = { x0: snap(wx), y0: snap(wy), x1: snap(wx), y1: snap(wy) };
    canvas2d.setPointerCapture(e.pointerId);
    return;
  }

  // 節點編輯：控制桿 → 節點
  if (State.nodeEdit === State.selectedId && State.selectedId != null) {
    const nh = hitNodeHandle(px, py);
    if (nh) { beginDrag(); dragNode = { id: State.selectedId, ...nh, mode: 'handle' }; canvas2d.setPointerCapture(e.pointerId); return; }
    const ai = hitAnchor(px, py);
    if (ai >= 0) { beginDrag(); dragNode = { id: State.selectedId, vi: ai, mode: e.altKey ? 'pull' : 'anchor' }; canvas2d.setPointerCapture(e.pointerId); return; }
  }

  // 縮放控點
  const rh = hitResizeHandle(px, py);
  if (rh) {
    beginDrag();
    dragResize = { id: State.selectedId, hid: rh };
    canvas2d.setPointerCapture(e.pointerId);
    return;
  }

  const hit = hitPart2D(wx, wy);
  if (hit) {
    selectPart(hit.id);
    beginDrag();
    drag2d = { id: hit.id, dx: wx - hit.layoutX, dy: wy - hit.layoutY };
    canvas2d.setPointerCapture(e.pointerId);
  } else if (e.button === 0) {
    selectPart(null);
    pan2d = { px, py, offX: State.view2d.offX, offY: State.view2d.offY };
    canvas2d.setPointerCapture(e.pointerId);
  }
});

canvas2d.addEventListener('pointermove', (e) => {
  const rect = canvas2d.getBoundingClientRect();
  const px = e.clientX - rect.left, py = e.clientY - rect.top;
  if (State.drawMode) {
    const dm = State.drawMode;
    const [wx, wy] = s2w(px, py);
    if (dm.penDrag) {
      // Illustrator 鋼筆：按住拖曳 → 以對稱控制桿建立平滑節點
      const v = dm.penDrag.v;
      v.hox = wx - dm.penDrag.ax; v.hoy = wy - dm.penDrag.ay;
      v.hix = -v.hox; v.hiy = -v.hoy;
    } else {
      dm.cursor = { x: snap(wx), y: snap(wy) };
    }
    draw2D(); return;
  }
  if (State.placeMode && State.placeDrag) {
    const [wx, wy] = s2w(px, py);
    State.placeDrag.x1 = snap(wx); State.placeDrag.y1 = snap(wy);
    draw2D(); return;
  }
  if (dragNode) {
    const p = getPart(dragNode.id); if (!p) return;
    const [wx, wy] = s2w(px, py);
    const loc = invNest(p, wx, wy);
    const v = p.verts[dragNode.vi];
    if (dragNode.mode === 'handle') setNodeHandle(v, dragNode.which, loc.x - v.x, loc.y - v.y, e.altKey);
    else if (dragNode.mode === 'pull') { v.hox = loc.x - v.x; v.hoy = loc.y - v.y; v.hix = -v.hox; v.hiy = -v.hoy; }
    else { v.x = snap(loc.x); v.y = snap(loc.y); }   // 移動節點
    buildPartMesh(p); assignSlabFromLayout(p); applyPartTexture(p); draw2D(); updateStats();
    return;
  }
  if (dragResize) {
    const p = getPart(dragResize.id); if (!p) return;
    const [wx, wy] = s2w(px, py);
    const loc = invNest(p, wx, wy);
    applyResize(p, dragResize.hid, loc.x, loc.y);
    buildPartMesh(p); assignSlabFromLayout(p); applyPartTexture(p); draw2D(); updateStats();
    return;
  }
  if (drag2d) {
    const [wx, wy] = s2w(px, py);
    const p = getPart(drag2d.id);
    p.layoutX = snap(wx - drag2d.dx); p.layoutY = snap(wy - drag2d.dy);
    assignSlabFromLayout(p); applyPartTexture(p); draw2D(); updateStats();
  } else if (pan2d) {
    State.view2d.offX = pan2d.offX + (px - pan2d.px);
    State.view2d.offY = pan2d.offY + (py - pan2d.py);
    draw2D();
  }
});

canvas2d.addEventListener('pointerup', () => {
  if (State.placeMode && State.placeDrag) { finishPlace(); return; }
  if (drag2d) {
    const p = getPart(drag2d.id);
    setStatus(p.slabId ? `「${p.name}」已排到 ${State.slabs.find(s => s.id === p.slabId).name}，紋理已套用。` : `「${p.name}」在待排區（無紋理）。`);
  }
  if (State.drawMode && State.drawMode.penDrag) { State.drawMode.penDrag = null; draw2D(); return; }
  if (dragResize) { const p = getPart(dragResize.id); const b = bbox(p); selectPart(dragResize.id); updatePropPanel(); setStatus(`已縮放「${p.name}」→ ${cm(b.w)}×${cm(b.h)} cm。`); }
  if (dragNode) { setStatus('節點編輯：拖節點移動、拖控制桿調曲率（Alt 拖＝獨立方向/角點）。'); }
  if (drag2d || dragResize || dragNode) commitDrag();
  drag2d = null; pan2d = null; dragResize = null; dragNode = null;
});

canvas2d.addEventListener('wheel', (e) => {
  e.preventDefault();
  const rect = canvas2d.getBoundingClientRect();
  const px = e.clientX - rect.left, py = e.clientY - rect.top;
  const [wx, wy] = s2w(px, py);
  const f = e.deltaY < 0 ? 1.12 : 1 / 1.12;
  State.view2d.scale *= f;
  State.view2d.offX = px - wx * State.view2d.scale;
  State.view2d.offY = py - wy * State.view2d.scale;
  draw2D();
}, { passive: false });

canvas2d.addEventListener('dblclick', (e) => {
  if (State.drawMode) { finishPolygon(); return; }
  const rect = canvas2d.getBoundingClientRect();
  const [wx, wy] = s2w(e.clientX - rect.left, e.clientY - rect.top);
  const hit = hitPart2D(wx, wy);
  if (hit) enterNodeEdit(hit.id);
});

function hitPart2D(wx, wy) {
  for (let i = State.parts.length - 1; i >= 0; i--) {
    const p = State.parts[i];
    const pts = flattenLocal(p.verts).map(v => nestPoint(p, v.x, v.y));
    if (pointInPoly(wx, wy, pts)) return p;
  }
  return null;
}
// ---- 縮放控點（外框 bounding-box）----
// 4 角(雙軸) + 4 邊中(單軸)，每個含固定的對側錨點(ax,ay)與作用軸
function resizeHandles(part) {
  const b = bbox(part);
  const { minx, miny, maxx, maxy } = b, mx = (minx + maxx) / 2, my = (miny + maxy) / 2;
  return [
    { id: 'tl', x: minx, y: miny, ax: maxx, ay: maxy, sx: true, sy: true },
    { id: 'tr', x: maxx, y: miny, ax: minx, ay: maxy, sx: true, sy: true },
    { id: 'br', x: maxx, y: maxy, ax: minx, ay: miny, sx: true, sy: true },
    { id: 'bl', x: minx, y: maxy, ax: maxx, ay: miny, sx: true, sy: true },
    { id: 't', x: mx, y: miny, ax: mx, ay: maxy, sx: false, sy: true },
    { id: 'b', x: mx, y: maxy, ax: mx, ay: miny, sx: false, sy: true },
    { id: 'l', x: minx, y: my, ax: maxx, ay: my, sx: true, sy: false },
    { id: 'r', x: maxx, y: my, ax: minx, ay: my, sx: true, sy: false },
  ];
}
function hitResizeHandle(px, py) {
  const p = getPart(State.selectedId);
  if (!p || State.drawMode) return null;
  for (const h of resizeHandles(p)) {
    const [hx, hy] = localToScreen(p, h.x, h.y);
    if (Math.hypot(px - hx, py - hy) <= 7) return h.id;
  }
  return null;
}
// 縮放：把選取零件依錨點縮放，使被拖角/邊到達游標(本地座標)
function applyResize(part, hid, lx, ly) {
  const h = resizeHandles(part).find(x => x.id === hid);
  if (!h) return;
  let sx = 1, sy = 1;
  if (h.sx) sx = (lx - h.ax) / ((h.x - h.ax) || 1e-6);
  if (h.sy) sy = (ly - h.ay) / ((h.y - h.ay) || 1e-6);
  const b = bbox(part);
  if (h.sx) { if (sx < 0.02) sx = 0.02; if (sx * b.w < 1) return; }
  if (h.sy) { if (sy < 0.02) sy = 0.02; if (sy * b.h < 1) return; }
  part.verts.forEach(v => {
    if (h.sx) { v.x = h.ax + (v.x - h.ax) * sx; v.hox *= sx; v.hix *= sx; }
    if (h.sy) { v.y = h.ay + (v.y - h.ay) * sy; v.hoy *= sy; v.hiy *= sy; }
  });
}

// ---- 節點編輯命中 ----
function hitNodeHandle(px, py) {
  const p = getPart(State.selectedId);
  if (!p || State.nodeEdit !== p.id) return null;
  for (let i = 0; i < p.verts.length; i++) {
    const v = p.verts[i];
    if (v.hox || v.hoy) { const [ox, oy] = localToScreen(p, v.x + v.hox, v.y + v.hoy); if (Math.hypot(px - ox, py - oy) <= 7) return { vi: i, which: 'out' }; }
    if (v.hix || v.hiy) { const [ix, iy] = localToScreen(p, v.x + v.hix, v.y + v.hiy); if (Math.hypot(px - ix, py - iy) <= 7) return { vi: i, which: 'in' }; }
  }
  return null;
}
function hitAnchor(px, py) {
  const p = getPart(State.selectedId);
  if (!p || State.nodeEdit !== p.id) return -1;
  for (let i = 0; i < p.verts.length; i++) {
    const [ax, ay] = localToScreen(p, p.verts[i].x, p.verts[i].y);
    if (Math.hypot(px - ax, py - ay) <= 7) return i;
  }
  return -1;
}
// 設定節點 i 的控制桿（dragging 'out' 或 'in'），預設對稱，break=true 拆成獨立
function setNodeHandle(v, which, dx, dy, brk) {
  if (which === 'out') { v.hox = dx; v.hoy = dy; if (!brk) { v.hix = -dx; v.hiy = -dy; } }
  else { v.hix = dx; v.hiy = dy; if (!brk) { v.hox = -dx; v.hoy = -dy; } }
}

function assignSlabFromLayout(p) {
  const bb = bbox(p);
  const c = nestPoint(p, bb.cx, bb.cy);
  let found = null;
  for (const s of State.slabs) {
    if (c.x >= s.originX && c.x <= s.originX + s.widthIn && c.y >= s.originY && c.y <= s.originY + s.heightIn) { found = s; break; }
  }
  p.slabId = found ? found.id : null;
}

/* ---------- 多邊形繪製 ---------- */
/* ---------- 拖曳建立矩形 / 三角 ---------- */
function startPlace(kind) {
  if (State.placeMode === kind) { cancelPlace(); return; }   // 再按一次取消
  cancelPlace();
  if (State.drawMode) cancelDraw();
  if (State.nodeEdit) exitNodeEdit();
  clearGizmoMode();
  State.placeMode = kind; State.placeDrag = null;
  $('addPartBtn').classList.toggle('armed', kind === 'rect');
  $('addTriBtn').classList.toggle('armed', kind === 'tri');
  setStatus(`${kind === 'rect' ? '矩形' : '三角'}：在畫布上按住拖曳拉出大小，放開即建立。Esc 取消。`);
}
function cancelPlace() {
  State.placeMode = null; State.placeDrag = null;
  $('addPartBtn').classList.remove('armed'); $('addTriBtn').classList.remove('armed');
  draw2D();
}
function finishPlace() {
  const d = State.placeDrag, kind = State.placeMode;
  State.placeDrag = null;
  const minx = Math.min(d.x0, d.x1), miny = Math.min(d.y0, d.y1);
  const w = Math.abs(d.x1 - d.x0), h = Math.abs(d.y1 - d.y0);
  if (w < 2 || h < 2) { setStatus('拖曳範圍太小，請再拖一次（或 Esc 取消）。'); draw2D(); return; }
  pushSnap(snapshot());
  const verts = kind === 'tri' ? triVerts(w, h) : rectVerts(w, h);
  const name = `${kind === 'tri' ? '三角' : '矩形'} ${State.nextId}`;
  const part = makePart({ name, verts, layoutX: minx, layoutY: miny });
  assignSlabFromLayout(part); applyPartTexture(part);
  cancelPlace();                 // 建立成功後離開建立模式
  selectPart(part.id); updateStats();
  setStatus(`已建立${kind === 'tri' ? '三角' : '矩形'}（${cm(w)}×${cm(h)} cm）。`);
}
function drawPlacePreview() {
  const d = State.placeDrag; if (!d) return;
  const minx = Math.min(d.x0, d.x1), miny = Math.min(d.y0, d.y1), maxx = Math.max(d.x0, d.x1), maxy = Math.max(d.y0, d.y1);
  const [ax, ay] = w2s(minx, miny), [bx, by] = w2s(maxx, maxy);
  ctx.save();
  ctx.fillStyle = 'rgba(78,161,255,.18)'; ctx.strokeStyle = '#4ea1ff'; ctx.lineWidth = 1.5; ctx.setLineDash([5, 4]);
  ctx.beginPath();
  if (State.placeMode === 'tri') { ctx.moveTo(ax, by); ctx.lineTo(bx, by); ctx.lineTo(ax, ay); ctx.closePath(); }
  else ctx.rect(ax, ay, bx - ax, by - ay);
  ctx.fill(); ctx.stroke();
  ctx.restore();
  ctx.fillStyle = '#cfe3ff'; ctx.font = '11px Segoe UI';
  ctx.fillText(`${cm(maxx - minx)}×${cm(maxy - miny)} cm`, bx + 6, by);
}

function toggleDrawMode() {
  if (State.placeMode) cancelPlace();
  if (State.drawMode) { finishPolygon(); return; }
  clearGizmoMode();
  State.drawMode = { pts: [], cursor: null, penDrag: null };
  State.nodeEdit = null;
  $('polyBtn').classList.add('armed');
  $('drawToolbar').hidden = false;
  updateDrawInfo();
  setStatus('鋼筆：點一下=角點、按住拖曳=弧線(平滑節點)。點回起點圈圈/Enter/雙擊完成，Esc 取消。');
}
function cancelDraw() {
  State.drawMode = null; $('polyBtn').classList.remove('armed'); $('drawToolbar').hidden = true;
  draw2D(); setStatus('已取消繪製。');
}
function finishPolygon() {
  const dm = State.drawMode; State.drawMode = null;
  $('polyBtn').classList.remove('armed'); $('drawToolbar').hidden = true;
  if (!dm) return;
  // 去除尾端與起點/前點過近的重複點（雙擊會多塞點）
  let pts = dm.pts.slice();
  const near = (a, b) => Math.hypot(a.x - b.x, a.y - b.y) < 0.5;
  while (pts.length >= 2 && near(pts[pts.length - 1], pts[pts.length - 2])) pts.pop();
  if (pts.length >= 2 && near(pts[pts.length - 1], pts[0])) pts.pop();
  if (pts.length < 3) { setStatus('多邊形已取消（至少需 3 個不同點）。'); draw2D(); return; }
  let minx = Infinity, miny = Infinity;
  pts.forEach(p => { minx = Math.min(minx, p.x); miny = Math.min(miny, p.y); });
  const verts = pts.map(p => ({ x: p.x - minx, y: p.y - miny, hox: p.hox || 0, hoy: p.hoy || 0, hix: p.hix || 0, hiy: p.hiy || 0 }));
  pushSnap(snapshot());
  const part = makePart({ name: `多邊形 ${State.nextId}`, verts, layoutX: minx, layoutY: miny });
  assignSlabFromLayout(part); applyPartTexture(part); draw2D(); updateStats();
  setStatus(`多邊形零件已建立（${verts.length} 節點），已同步到右側 3D。雙擊零件可進入節點編輯調整貝茲曲線。`);
}

/* ===================================================================
   選取 / 屬性面板
   =================================================================== */
function getPart(id) { return State.parts.find(p => p.id === id); }

function selectPart(id) {
  State.selectedId = id;
  if (id !== State.nodeEdit) State.nodeEdit = null;   // 切換零件即離開節點編輯
  for (const p of State.parts) if (p.outline) p.outline.visible = (p.id === id);
  updatePropPanel(); draw2D();
}

function updatePropPanel() {
  const p = getPart(State.selectedId);
  $('noSelect').hidden = !!p; $('propForm').hidden = !p;
  if (!p) return;
  const bb = bbox(p);
  $('pName').value = p.name;
  $('pWidth').value = cm(bb.w);
  $('pDepth').value = cm(bb.h);
  $('pThick').value = cm(p.thickIn);
  $('pElev').value = cm(p.elevIn);
  const m2 = (polyArea(p.verts) * SQIN2M2).toFixed(3);
  const slab = State.slabs.find(s => s.id === p.slabId);
  const isPoly = p.verts.length !== 4 || !isAxisRect(p);
  const deg = (r) => Math.round((r || 0) / D2R);
  $('pReadout').textContent =
    `${p.verts.length} 邊 · 面積 ${m2} m² · 平面旋轉 ${(+p.rot2d).toFixed(0)}° · 3D旋轉 Y${deg(p.rotY)}/X${deg(p.tiltX)}/Z${deg(p.tiltZ)}° · 石材：${slab ? slab.name : '無'}${isPoly ? ' · (多邊形：改尺寸會轉成矩形)' : ''}`;
}

function isAxisRect(p) {
  if (p.verts.length !== 4) return false;
  const xs = new Set(p.verts.map(v => +v.x.toFixed(3)));
  const ys = new Set(p.verts.map(v => +v.y.toFixed(3)));
  return xs.size === 2 && ys.size === 2;
}

function bindPropInputs() {
  const setDim = (which, valCm) => {
    const p = getPart(State.selectedId); if (!p) return;
    const val = Math.max(0.5, inFromCm(valCm));        // cm → 英吋
    pushSnap(snapshot());
    const bb = bbox(p);
    // 改寬/深：以矩形重建（多邊形會被轉成矩形）
    const w = which === 'w' ? val : bb.w, d = which === 'd' ? val : bb.h;
    p.verts = rectVerts(w, d);
    buildPartMesh(p); rebuild2DLayout(); updatePropPanel();
  };
  $('pName').addEventListener('input', e => { const p = getPart(State.selectedId); if (p) { p.name = e.target.value; draw2D(); } });
  $('pWidth').addEventListener('change', e => setDim('w', e.target.value));
  $('pDepth').addEventListener('change', e => setDim('d', e.target.value));
  $('pThick').addEventListener('change', e => { const p = getPart(State.selectedId); if (p) { pushSnap(snapshot()); p.thickIn = Math.max(0.05, inFromCm(e.target.value)); buildPartMesh(p); updatePropPanel(); } });
  $('pElev').addEventListener('change', e => { const p = getPart(State.selectedId); if (p) { pushSnap(snapshot()); p.elevIn = inFromCm(e.target.value); updatePartTransform(p); updateGizmo(); updatePropPanel(); } });
}

/* ===================================================================
   3D 指標：選取 / 拖曳 / 邊線接合
   =================================================================== */
let drag3d = null, rotDrag = null;
function setup3DPointer() {
  const el = renderer.domElement;
  el.addEventListener('pointerdown', (e) => {
    if (e.button !== 0) return;
    if (State.standPick) { handleStandPick(e); return; }
    if (State.edgeOrient) { handleEdgePick(e); return; }
    // 旋轉圓環
    if (State.gizmoMode === 'rotate' && gizmo.group.visible) {
      const gi = pickGizmo(e); if (gi) { startRotDrag(gi.axis, e); return; }
    }
    // 移動箭頭
    if (State.gizmoMode === 'move' && moveG.group.visible) {
      const mi = pickMoveGizmo(e); if (mi) { startMoveDrag(mi.axis, e); return; }
    }
    const inter = pick3D(e);
    if (inter) {
      const pid = inter.object.userData.partId;
      selectPart(pid);
      const p = getPart(pid), pt = groundPoint(e);
      if (p && pt) { beginDrag(); drag3d = { id: pid, dx: pt.x - p.pos3d.x, dz: pt.z - p.pos3d.z }; controls.enabled = false; }
    }
  });
  el.addEventListener('pointermove', (e) => {
    if (rotDrag) { rotDragMove(e); return; }
    if (moveDrag) { moveDragMove(e); return; }
    if (drag3d) {
      const p = getPart(drag3d.id); if (!p) return;
      const pt = groundPoint(e); if (!pt) return;
      p.pos3d.x = pt.x - drag3d.dx; p.pos3d.z = pt.z - drag3d.dz;
      updatePartTransform(p); return;
    }
    if (State.gizmoMode === 'rotate' && gizmo.group.visible) { const gi = pickGizmo(e); setGizmoHover(gi ? gi.axis : null); el.style.cursor = gi ? 'grab' : ''; }
    else if (State.gizmoMode === 'move' && moveG.group.visible) { const mi = pickMoveGizmo(e); setMoveHover(mi ? mi.axis : null); el.style.cursor = mi ? 'grab' : ''; }
  });
  el.addEventListener('pointerup', () => {
    if (rotDrag) { commitDrag(); rotDrag = null; hideBadge(); hideTickRing(); }
    if (moveDrag) { commitDrag(); moveDrag = null; hideBadge(); }
    if (drag3d) commitDrag();
    drag3d = null; controls.enabled = true;
  });
}

/* ---------------- 旋轉 Gizmo (Tinkercad 風) ---------------- */
const GAX = { x: 0xff5d6c, y: 0x59e36b, z: 0x4ea1ff };
let gizmo = null, tickRing = null;
function buildGizmo() {
  gizmo = { group: new THREE.Group(), rings: {}, forId: null, R: 0 };
  gizmo.group.visible = false;
  const mk = (axis, euler) => {
    const mat = new THREE.MeshBasicMaterial({ color: GAX[axis], transparent: true, opacity: 0.55, depthTest: false });
    const m = new THREE.Mesh(new THREE.TorusGeometry(10, 0.5, 10, 120), mat);
    m.rotation.copy(euler); m.renderOrder = 998; m.userData.axis = axis;
    gizmo.rings[axis] = m; gizmo.group.add(m);
  };
  mk('y', new THREE.Euler(Math.PI / 2, 0, 0));   // 繞 Y（水平環）
  mk('x', new THREE.Euler(0, Math.PI / 2, 0));   // 繞 X
  mk('z', new THREE.Euler(0, 0, 0));             // 繞 Z
  scene.add(gizmo.group);
}
function rebuildGizmoRings(R) {
  const tube = Math.max(0.18, R * 0.012);     // 細線
  for (const axis of ['x', 'y', 'z']) {
    const m = gizmo.rings[axis];
    if (m.geometry) m.geometry.dispose();
    m.geometry = new THREE.TorusGeometry(R, tube, 8, 160);
  }
}
function updateGizmo() {
  const p = getPart(State.selectedId);
  const baseHide = !p || State.drawMode || State.placeMode || State.nodeEdit || State.edgeOrient || State.standPick;
  const showRot = !baseHide && State.gizmoMode === 'rotate';
  const showMove = !baseHide && State.gizmoMode === 'move';
  if (gizmo) gizmo.group.visible = showRot;
  if (moveG) moveG.group.visible = showMove;
  if (!showRot && !showMove) return;
  const bb = bbox(p);
  const R = Math.max(bb.w, bb.h) / 2 + 6;
  if (showRot) {
    if (gizmo.forId !== p.id || Math.abs(gizmo.R - R) > 0.01) { rebuildGizmoRings(R); gizmo.forId = p.id; gizmo.R = R; }
    gizmo.group.position.copy(p.group.position);
  }
  if (showMove) {
    moveG.group.position.copy(p.group.position);
    moveG.group.scale.setScalar(R / 9.5);
  }
}
function clearGizmoMode() {
  State.gizmoMode = null;
  $('moveBtn').classList.remove('active'); $('rot3dBtn').classList.remove('active');
}
function setGizmoMode(mode) {
  State.gizmoMode = (State.gizmoMode === mode) ? null : mode;
  $('moveBtn').classList.toggle('active', State.gizmoMode === 'move');
  $('rot3dBtn').classList.toggle('active', State.gizmoMode === 'rotate');
  if (State.gizmoMode && !getPart(State.selectedId)) setStatus('請先選一個零件，再使用移動 / 旋轉。');
  else if (State.gizmoMode === 'move') setStatus('移動：拖曳 XYZ 箭頭沿該軸移動（綠 Y=上下）。');
  else if (State.gizmoMode === 'rotate') setStatus('旋轉：拖曳圓環旋轉（吸附 22.5°，Shift 微調）。');
  updateGizmo();
}
function setGizmoHover(axis) {
  if (!gizmo) return;
  for (const a of ['x', 'y', 'z']) gizmo.rings[a].material.opacity = (a === axis) ? 1.0 : 0.55;
}

/* ---------------- 移動 Gizmo (XYZ 箭頭) ---------------- */
let moveG = null, moveMeshes = [], moveDrag = null;
function buildMoveGizmo() {
  moveG = { group: new THREE.Group(), axes: {} };
  moveG.group.visible = false; moveMeshes = [];
  const mk = (axis, euler) => {
    const g = new THREE.Group();
    const mat = new THREE.MeshBasicMaterial({ color: GAX[axis], transparent: true, opacity: 0.92, depthTest: false });
    const shaft = new THREE.Mesh(new THREE.CylinderGeometry(0.35, 0.35, 8, 12), mat);
    shaft.position.y = 4;
    const head = new THREE.Mesh(new THREE.ConeGeometry(1.3, 3, 16), mat);
    head.position.y = 9.5;
    [shaft, head].forEach(m => { m.renderOrder = 998; m.userData.axis = axis; moveMeshes.push(m); });
    g.add(shaft); g.add(head); g.rotation.copy(euler); g.userData.axis = axis;
    moveG.axes[axis] = g; moveG.group.add(g);
  };
  mk('x', new THREE.Euler(0, 0, -Math.PI / 2));
  mk('y', new THREE.Euler(0, 0, 0));
  mk('z', new THREE.Euler(Math.PI / 2, 0, 0));
  scene.add(moveG.group);
}
function setMoveHover(axis) {
  if (!moveG) return;
  for (const a of ['x', 'y', 'z']) moveG.axes[a].children.forEach(m => m.material.opacity = (a === axis) ? 1.0 : 0.92);
}
function pickMoveGizmo(e) {
  raycaster.setFromCamera(ndc(e), camera);
  const hits = raycaster.intersectObjects(moveMeshes, false);
  return hits.length ? { axis: hits[0].object.userData.axis } : null;
}
// 滑鼠射線與某世界軸線最近點在軸上的參數 t
function closestAxisT(e, center, axis) {
  raycaster.setFromCamera(ndc(e), camera);
  const ro = raycaster.ray.origin, rd = raycaster.ray.direction;
  const w0 = new THREE.Vector3().subVectors(center, ro);
  const b = axis.dot(rd), d = axis.dot(w0), eDot = rd.dot(w0);
  const denom = 1 - b * b;                 // a=1, c=1
  if (Math.abs(denom) < 1e-6) return null;
  return (b * eDot - d) / denom;
}
function startMoveDrag(axis, e) {
  const p = getPart(State.selectedId); if (!p) return;
  const center = p.group.position.clone();
  const axisVec = axisVecOf(axis);
  const t0 = closestAxisT(e, center, axisVec); if (t0 === null) return;
  beginDrag();
  moveDrag = { id: p.id, axis, axisVec, center, t0, baseX: p.pos3d.x, baseZ: p.pos3d.z, baseElev: p.elevIn };
  controls.enabled = false; setMoveHover(axis);
}
function moveDragMove(e) {
  const p = getPart(moveDrag.id); if (!p) return;
  const t = closestAxisT(e, moveDrag.center, moveDrag.axisVec); if (t === null) return;
  const d = t - moveDrag.t0;
  if (moveDrag.axis === 'x') p.pos3d.x = moveDrag.baseX + d;
  else if (moveDrag.axis === 'z') p.pos3d.z = moveDrag.baseZ + d;
  else p.elevIn = moveDrag.baseElev + d;
  updatePartTransform(p);
  showBadge(e, `${moveDrag.axis.toUpperCase()} ${d >= 0 ? '+' : ''}${(d * IN2CM).toFixed(1)} cm`);
}
function pickGizmo(e) {
  raycaster.setFromCamera(ndc(e), camera);
  const hits = raycaster.intersectObjects([gizmo.rings.x, gizmo.rings.y, gizmo.rings.z], false);
  return hits.length ? { axis: hits[0].object.userData.axis } : null;
}
function axisVecOf(axis) { return axis === 'x' ? new THREE.Vector3(1, 0, 0) : axis === 'y' ? new THREE.Vector3(0, 1, 0) : new THREE.Vector3(0, 0, 1); }
function gizmoPlanePoint(e, center, normal) {
  raycaster.setFromCamera(ndc(e), camera);
  const pl = new THREE.Plane().setFromNormalAndCoplanarPoint(normal, center);
  const pt = new THREE.Vector3();
  return raycaster.ray.intersectPlane(pl, pt) ? pt : null;
}
function startRotDrag(axis, e) {
  const p = getPart(State.selectedId); if (!p) return;
  const center = p.group.position.clone();
  const axisVec = axisVecOf(axis);
  let u = axis === 'y' ? new THREE.Vector3(0, 0, 1) : new THREE.Vector3(0, 1, 0);
  const v = new THREE.Vector3().crossVectors(axisVec, u).normalize();
  u = new THREE.Vector3().crossVectors(v, axisVec).normalize();
  const pt = gizmoPlanePoint(e, center, axisVec);
  const ang = pt ? Math.atan2(pt.clone().sub(center).dot(v), pt.clone().sub(center).dot(u)) : 0;
  beginDrag();
  rotDrag = { id: p.id, axis, center, axisVec, u, v, last: ang, accum: 0, baseRotY: p.rotY, baseTiltX: p.tiltX, baseTiltZ: p.tiltZ };
  controls.enabled = false;
  setGizmoHover(axis);
  showTickRing(center, u, v, gizmo.R);
}
function rotDragMove(e) {
  const p = getPart(rotDrag.id); if (!p) return;
  const pt = gizmoPlanePoint(e, rotDrag.center, rotDrag.axisVec); if (!pt) return;
  const ang = Math.atan2(pt.clone().sub(rotDrag.center).dot(rotDrag.v), pt.clone().sub(rotDrag.center).dot(rotDrag.u));
  let diff = Math.atan2(Math.sin(ang - rotDrag.last), Math.cos(ang - rotDrag.last));
  rotDrag.accum += diff; rotDrag.last = ang;
  const snapDeg = e.shiftKey ? 1 : 22.5;
  const deg = Math.round((rotDrag.accum / D2R) / snapDeg) * snapDeg;
  const rad = deg * D2R;
  if (rotDrag.axis === 'y') p.rotY = rotDrag.baseRotY + rad;
  else if (rotDrag.axis === 'x') p.tiltX = rotDrag.baseTiltX + rad;
  else p.tiltZ = rotDrag.baseTiltZ + rad;
  updatePartTransform(p);
  showBadge(e, `${deg > 0 ? '+' : ''}${deg}°`);
}

/* 角度量角器刻度環 + 角度數字 */
function showTickRing(center, u, v, R) {
  hideTickRing();
  const pts = [];
  for (let i = 0; i < 48; i++) {
    const a = i / 48 * Math.PI * 2, major = (i % 3 === 0);
    const dir = u.clone().multiplyScalar(Math.cos(a)).add(v.clone().multiplyScalar(Math.sin(a)));
    pts.push(center.clone().add(dir.clone().multiplyScalar(R * 1.02)));
    pts.push(center.clone().add(dir.clone().multiplyScalar(R * (major ? 1.14 : 1.07))));
  }
  const g = new THREE.BufferGeometry().setFromPoints(pts);
  tickRing = new THREE.LineSegments(g, new THREE.LineBasicMaterial({ color: 0xffffff, transparent: true, opacity: 0.5, depthTest: false }));
  tickRing.renderOrder = 997; scene.add(tickRing);
}
function hideTickRing() { if (tickRing) { scene.remove(tickRing); tickRing.geometry.dispose(); tickRing.material.dispose(); tickRing = null; } }
function showBadge(e, text) {
  const b = $('rotBadge'); if (!b) return;
  const rect = renderer.domElement.getBoundingClientRect();
  b.style.display = 'block';
  b.style.left = (e.clientX - rect.left + 14) + 'px';
  b.style.top = (e.clientY - rect.top - 10) + 'px';
  b.textContent = text;
}
function hideBadge() { const b = $('rotBadge'); if (b) b.style.display = 'none'; }

function ndc(e) {
  const r = renderer.domElement.getBoundingClientRect();
  return new THREE.Vector2(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1);
}
function pick3D(e) {
  raycaster.setFromCamera(ndc(e), camera);
  const meshes = [];
  State.parts.forEach(p => { meshes.push(p.body); if (p.topSkin.visible) meshes.push(p.topSkin); });
  const hits = raycaster.intersectObjects(meshes, false);
  return hits.length ? hits[0] : null;
}
function groundPoint(e) {
  raycaster.setFromCamera(ndc(e), camera);
  const pt = new THREE.Vector3();
  return raycaster.ray.intersectPlane(new THREE.Plane(new THREE.Vector3(0, 1, 0), 0), pt) ? pt : null;
}

/* 邊在世界的真實 3D 端點（取頂面多邊形頂點） */
function edgeWorld3D(part, ei) {
  part.group.updateMatrixWorld(true);
  const bb = bbox(part), n = part.verts.length;
  const v0 = part.verts[ei], v1 = part.verts[(ei + 1) % n];
  const a = part.topSkin.localToWorld(new THREE.Vector3(v0.x - bb.cx, v0.y - bb.cy, 0));
  const b = part.topSkin.localToWorld(new THREE.Vector3(v1.x - bb.cx, v1.y - bb.cy, 0));
  return [a, b];
}
// 零件多邊形形心的世界座標（用於判斷在邊的哪一側）
function partCentroidWorld(part) {
  const bb = bbox(part); let mx = 0, my = 0;
  for (const v of part.verts) { mx += v.x; my += v.y; }
  mx /= part.verts.length; my /= part.verts.length;
  return part.topSkin.localToWorld(new THREE.Vector3(mx - bb.cx, my - bb.cy, 0));
}
function distToSeg3D(p, a, b) {
  const ab = b.clone().sub(a);
  let t = p.clone().sub(a).dot(ab) / (ab.lengthSq() || 1e-6);
  t = Math.max(0, Math.min(1, t));
  return p.distanceTo(a.clone().add(ab.multiplyScalar(t)));
}
function nearestEdge3D(part, point) {
  let best = 0, bd = Infinity;
  for (let i = 0; i < part.verts.length; i++) {
    const [a, b] = edgeWorld3D(part, i);
    const d = distToSeg3D(point, a, b);
    if (d < bd) { bd = d; best = i; }
  }
  return best;
}

/* 選取邊的高亮線 */
let edgeHL = { src: null, dst: null };
function showEdgeHL(key, pts, color) {
  hideEdgeHL(key);
  const g = new THREE.BufferGeometry().setFromPoints(pts);
  const m = new THREE.LineBasicMaterial({ color, depthTest: false, transparent: true });
  const line = new THREE.Line(g, m); line.renderOrder = 999; scene.add(line);
  // 端點小球，視覺更清楚
  const dots = pts.map(p => { const s = new THREE.Mesh(new THREE.SphereGeometry(1.4, 10, 8), new THREE.MeshBasicMaterial({ color, depthTest: false })); s.position.copy(p); s.renderOrder = 999; scene.add(s); return s; });
  edgeHL[key] = { line, dots };
}
function hideEdgeHL(key) {
  const h = edgeHL[key]; if (!h) return;
  scene.remove(h.line); h.line.geometry.dispose(); h.line.material.dispose();
  h.dots.forEach(d => { scene.remove(d); d.geometry.dispose(); d.material.dispose(); });
  edgeHL[key] = null;
}
function clearEdgeHL() { hideEdgeHL('src'); hideEdgeHL('dst'); }

function armEdgeOrient() {
  if (State.parts.length < 2) return setStatus('需要至少兩個零件才能邊線接合。');
  clearGizmoMode(); clearEdgeHL();
  State.edgeOrient = { stage: 'src', src: null };
  $('orientBtn').classList.add('armed');
  setStatus('邊線接合 ①：在 3D 點選「A 物件」要接合的邊（會移動 A 去拼 B）。');
}
function handleEdgePick(e) {
  const inter = pick3D(e);
  if (!inter) { setStatus('沒點到零件，請點零件表面靠近要接合的那條邊。'); return; }
  const part = getPart(inter.object.userData.partId);
  const ei = nearestEdge3D(part, inter.point);
  if (State.edgeOrient.stage === 'src') {
    selectPart(part.id);
    State.edgeOrient.src = { partId: part.id, edge: ei };
    State.edgeOrient.stage = 'dst';
    showEdgeHL('src', edgeWorld3D(part, ei), 0xffd000);
    setStatus('邊線接合 ②：再點「B 物件」要對齊的邊，兩邊會拼合在一起。');
  } else {
    if (part.id === State.edgeOrient.src.partId) { setStatus('請點「另一個」零件作為 B。'); return; }
    showEdgeHL('dst', edgeWorld3D(part, ei), 0x34c3ff);
    doEdgeWeld(State.edgeOrient.src, { partId: part.id, edge: ei });
    State.edgeOrient = null; $('orientBtn').classList.remove('armed');
    setTimeout(clearEdgeHL, 900);
  }
}

/* 選底邊立起：以選取的邊為底，繞該邊翻轉 90° 立起並落到工作平面 */
function armStandEdge() {
  if (!State.parts.length) return setStatus('沒有零件可立起。');
  clearGizmoMode(); clearEdgeHL();
  State.standPick = true;
  $('standEdgeBtn').classList.add('armed');
  setStatus('立起：在 3D 點選一條邊作為「底部」，零件會以該邊立起。Esc 取消。');
}
function handleStandPick(e) {
  const inter = pick3D(e);
  if (!inter) { setStatus('沒點到零件，請點零件表面靠近要當底部的那條邊。'); return; }
  const part = getPart(inter.object.userData.partId);
  const ei = nearestEdge3D(part, inter.point);
  selectPart(part.id);
  showEdgeHL('src', edgeWorld3D(part, ei), 0xffd000);
  standOnEdge(part, ei);
  State.standPick = false; $('standEdgeBtn').classList.remove('armed');
  setTimeout(clearEdgeHL, 700);
}
function standOnEdge(part, ei) {
  pushSnap(snapshot());
  part.group.updateMatrixWorld(true);
  const [a, b] = edgeWorld3D(part, ei);
  const pivot = a.clone().add(b).multiplyScalar(0.5);
  const axis = b.clone().sub(a).normalize();
  const qGroup = new THREE.Quaternion().setFromEuler(new THREE.Euler(part.tiltX || 0, part.rotY || 0, part.tiltZ || 0, 'XYZ'));
  const oldCenter = part.group.position.clone();
  const evalA = (ang) => {
    const Re = new THREE.Quaternion().setFromAxisAngle(axis, ang);
    const c = pivot.clone().add(oldCenter.clone().sub(pivot).applyQuaternion(Re));
    return { Re, c };
  };
  const c1 = evalA(Math.PI / 2), c2 = evalA(-Math.PI / 2);
  const best = (c1.c.y >= c2.c.y) ? c1 : c2;          // 往上立起的方向
  const qNew = best.Re.clone().multiply(qGroup);
  const eu = new THREE.Euler().setFromQuaternion(qNew, 'XYZ');
  part.tiltX = eu.x; part.rotY = eu.y; part.tiltZ = eu.z;
  part.pos3d.x = best.c.x; part.pos3d.z = best.c.z;
  part.elevIn = best.c.y - part.thickIn / 2;
  updatePartTransform(part);
  // 落到工作平面：最低點移到 y=0
  const box = new THREE.Box3().setFromObject(part.body);
  part.elevIn -= box.min.y;
  updatePartTransform(part); updateGizmo(); updatePropPanel();
  setStatus(`已以選取邊為底部立起「${part.name}」。`);
}

/* 邊線接合（純平移，不旋轉）：把 A 選取邊的中點平移到 B 選取邊的中點 */
function doEdgeWeld(src, dst) {
  const A = getPart(src.partId), B = getPart(dst.partId);
  pushSnap(snapshot());
  const [a1, a2] = edgeWorld3D(A, src.edge);
  const [b1, b2] = edgeWorld3D(B, dst.edge);
  const aMid = a1.clone().add(a2).multiplyScalar(0.5);
  const bMid = b1.clone().add(b2).multiplyScalar(0.5);
  const d = bMid.clone().sub(aMid);                       // 3D 平移量
  A.pos3d.x += d.x; A.pos3d.z += d.z; A.elevIn += d.y;
  updatePartTransform(A); updateGizmo();
  setStatus(`已將「${A.name}」平移接合到「${B.name}」的選取邊（不旋轉）。`);
}

/* ===================================================================
   Snap / Stack / 旋轉 / 立起 / 刪除
   =================================================================== */
function nearestOtherPart(p) {
  let best = null, bd = Infinity;
  for (const o of State.parts) {
    if (o.id === p.id) continue;
    const d = Math.hypot(o.pos3d.x - p.pos3d.x, o.pos3d.z - p.pos3d.z);
    if (d < bd) { bd = d; best = o; }
  }
  return best;
}
function doSnap() {
  const p = getPart(State.selectedId); if (!p) return setStatus('請先選一個零件。');
  const t = nearestOtherPart(p); if (!t) return setStatus('沒有其他零件可對齊。');
  pushSnap(snapshot());
  const tH = bbox(t).w / 2, pH = bbox(p).w / 2;
  const dir = p.pos3d.x >= t.pos3d.x ? 1 : -1;
  p.pos3d.x = t.pos3d.x + dir * (tH + pH + State.snapGapIn);
  p.pos3d.z = t.pos3d.z; p.elevIn = t.elevIn;
  updatePartTransform(p);
  setStatus(`已將「${p.name}」對齊「${t.name}」旁，間距 ${State.snapGapIn}"。`);
}
function rotate2d(big) {
  const p = getPart(State.selectedId); if (!p) return;
  pushSnap(snapshot());
  p.rot2d = (p.rot2d + (big ? 90 : 15)) % 360;
  assignSlabFromLayout(p); applyPartTexture(p); draw2D(); updatePropPanel();
  setStatus(`平面旋轉 → ${(+p.rot2d).toFixed(0)}°`);
}
function resetRot3D() {
  const p = getPart(State.selectedId); if (!p) return setStatus('請先選一個零件。');
  pushSnap(snapshot());
  p.rotY = 0; p.tiltX = 0; p.tiltZ = 0; updatePartTransform(p); updateGizmo();
  setStatus('已歸正零件的 3D 旋轉。');
}
function deleteSelected() {
  const p = getPart(State.selectedId); if (!p) return;
  pushSnap(snapshot());
  scene.remove(p.group); disposeGroup(p.group);
  State.parts = State.parts.filter(x => x.id !== p.id);
  State.selectedId = null; updatePropPanel(); rebuild2DLayout();
  setStatus('已刪除零件。');
}

/* ===================================================================
   石材匯入 / 清單
   =================================================================== */
$('addSlabInput').addEventListener('change', (e) => {
  const file = e.target.files[0]; if (!file) return;
  const name = file.name.replace(/\.[^.]+$/, '').slice(0, 16);
  const reader = new FileReader();
  reader.onload = () => {
    const img = new Image();
    img.onload = () => openSlabDialog(reader.result, img, name);
    img.src = reader.result;
  };
  reader.readAsDataURL(file);
  e.target.value = '';
});

/* ---- 匯入尺寸對話框 ---- */
let pendingSlab = null, sdPrevUnit = 'in';
const UNIT_IN = { in: 1, cm: 0.393701, mm: 0.0393701 };   // 1 單位 = ? 英吋
function openSlabDialog(src, img, name) {
  pendingSlab = { src, img, name, aspect: img.naturalWidth / img.naturalHeight };
  sdPrevUnit = 'cm';
  $('sdPreview').src = src;
  $('sdName').value = name || '';
  $('sdUnit').value = 'cm';
  $('sdLock').checked = true;
  $('sdW').value = 320;                                  // 預設 ~320cm 大板
  $('sdH').value = Math.round(320 / pendingSlab.aspect);
  $('slabDialog').hidden = false;
  setTimeout(() => $('sdW').focus(), 30);
}
function closeSlabDialog() { $('slabDialog').hidden = true; pendingSlab = null; }
function sdSyncFromW() { if ($('sdLock').checked && pendingSlab) $('sdH').value = +(+$('sdW').value / pendingSlab.aspect).toFixed(2); }
function sdSyncFromH() { if ($('sdLock').checked && pendingSlab) $('sdW').value = +(+$('sdH').value * pendingSlab.aspect).toFixed(2); }
$('sdW').addEventListener('input', sdSyncFromW);
$('sdH').addEventListener('input', sdSyncFromH);
$('sdUnit').addEventListener('change', () => {
  const to = $('sdUnit').value, f = UNIT_IN[sdPrevUnit] / UNIT_IN[to];   // 換算保持實際大小
  $('sdW').value = +(+$('sdW').value * f).toFixed(2);
  $('sdH').value = +(+$('sdH').value * f).toFixed(2);
  sdPrevUnit = to;
});
$('sdCancel').addEventListener('click', closeSlabDialog);
$('sdOk').addEventListener('click', confirmSlabDialog);
[$('sdW'), $('sdH'), $('sdName')].forEach(el => el.addEventListener('keydown', (e) => {
  if (e.key === 'Enter') confirmSlabDialog();
  if (e.key === 'Escape') closeSlabDialog();
}));
function confirmSlabDialog() {
  if (!pendingSlab) return;
  const u = $('sdUnit').value, k = UNIT_IN[u];
  const wIn = Math.max(1, +$('sdW').value * k), hIn = Math.max(1, +$('sdH').value * k);
  const name = ($('sdName').value.trim().slice(0, 16)) || pendingSlab.name || `Slab ${State.slabs.length + 1}`;
  pushSnap(snapshot());
  const slab = {
    id: State.nextId++, name, img: pendingSlab.img, src: pendingSlab.src,
    widthIn: Math.round(wIn * 100) / 100, heightIn: Math.round(hIn * 100) / 100,
    originX: 0, originY: 0, tex: null,
  };
  slabStore[slab.id] = { src: slab.src, img: slab.img };
  State.slabs.push(slab);
  renderSlabList(); rebuild2DLayout();
  setStatus(`已匯入石材「${name}」(${slab.widthIn}×${slab.heightIn} in)。`);
  closeSlabDialog();
}

function addSlabFromSrc(src, name, widthIn, heightIn, cb) {
  const img = new Image();
  img.onload = () => {
    const aspect = img.naturalWidth / img.naturalHeight;
    const w = widthIn || 126;
    const h = heightIn || Math.round(w / aspect);
    const slab = { id: State.nextId++, name: name || `Slab ${State.slabs.length + 1}`, img, src, widthIn: w, heightIn: h, originX: 0, originY: 0, tex: null };
    slabStore[slab.id] = { src, img };
    State.slabs.push(slab);
    renderSlabList(); rebuild2DLayout();
    setStatus(`已匯入石材「${slab.name}」(${w}×${h}in)。`);
    if (cb) cb(slab);
  };
  img.src = src;
}

function renderSlabList() {
  const list = $('slabList');
  if (!State.slabs.length) { list.innerHTML = '<span class="muted">尚未匯入石材，請點左側工具列「加入石材」</span>'; return; }
  list.innerHTML = '';
  for (const s of State.slabs) {
    const chip = document.createElement('div'); chip.className = 'slabChip';
    chip.innerHTML = `<img src="${s.src}"><span>${s.name}</span>
      <label>W<input type="number" value="${cm(s.widthIn)}" step="1"></label>
      <label>H<input type="number" value="${cm(s.heightIn)}" step="1"></label>
      <span class="muted" style="font-size:10px">cm</span>
      <span class="x" title="移除">✕</span>`;
    const [wIn, hIn] = chip.querySelectorAll('input');
    wIn.addEventListener('change', () => { pushSnap(snapshot()); s.widthIn = Math.max(1, inFromCm(wIn.value)); refreshAll(); });
    hIn.addEventListener('change', () => { pushSnap(snapshot()); s.heightIn = Math.max(1, inFromCm(hIn.value)); refreshAll(); });
    chip.querySelector('.x').addEventListener('click', () => removeSlab(s.id));
    list.appendChild(chip);
  }
}
function removeSlab(id) {
  pushSnap(snapshot());
  State.slabs = State.slabs.filter(s => s.id !== id);
  for (const p of State.parts) if (p.slabId === id) { p.slabId = null; applyPartTexture(p); }
  renderSlabList(); rebuild2DLayout();
}
function refreshAll() { for (const p of State.parts) applyPartTexture(p); rebuild2DLayout(); }

/* ===================================================================
   存檔 / 讀檔 (JSON)
   =================================================================== */
function saveProject() {
  const data = {
    version: 2, nextId: State.nextId,
    slabs: State.slabs.map(s => ({ id: s.id, name: s.name, src: s.src, widthIn: s.widthIn, heightIn: s.heightIn })),
    parts: State.parts.map(p => ({
      id: p.id, name: p.name, verts: p.verts, thickIn: p.thickIn, elevIn: p.elevIn,
      vertical: p.vertical, rot2d: p.rot2d, slabId: p.slabId, layoutX: p.layoutX, layoutY: p.layoutY,
      pos3d: p.pos3d, rotY: p.rotY, tiltX: p.tiltX || 0, tiltZ: p.tiltZ || 0,
    })),
  };
  const blob = new Blob([JSON.stringify(data)], { type: 'application/json' });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob); a.download = 'stone-layout.json'; a.click();
  setStatus('已匯出專案 JSON。');
}

/* ---- 輸出切版座標（cm，原點＝石材左上角）---- */
let exportData = null;
function slabLocalCm(p, s, lx, ly) {
  const w = nestPoint(p, lx, ly);
  return { x: +((w.x - s.originX) * IN2CM).toFixed(2), y: +((w.y - s.originY) * IN2CM).toFixed(2) };
}
function partExport(p, s) {
  const curved = p.verts.some(v => v.hox || v.hoy || v.hix || v.hiy);
  const vertices = p.verts.map(v => slabLocalCm(p, s, v.x, v.y));
  const outline = curved ? flattenLocal(p.verts).map(pt => slabLocalCm(p, s, pt.x, pt.y)) : vertices;
  return { name: p.name, curved, areaM2: +(polyArea(p.verts) * SQIN2M2).toFixed(3), vertices, outline };
}
function buildExport() {
  const slabs = State.slabs.map(s => ({
    name: s.name, widthCm: cm(s.widthIn), heightCm: cm(s.heightIn),
    parts: State.parts.filter(p => p.slabId === s.id).map(p => partExport(p, s)),
  }));
  const unplaced = State.parts.filter(p => !p.slabId).map(p => p.name);
  return { units: 'cm', origin: 'slab-top-left (X→right, Y→down)', slabs, unplaced };
}
function exportToText(d) {
  let t = `石材切版座標輸出\n單位：cm　原點：各石材左上角 (X→右, Y→下)\n`;
  for (const s of d.slabs) {
    t += `\n== 石材：${s.name}  (${s.widthCm} × ${s.heightCm} cm) ==\n`;
    if (!s.parts.length) { t += `  (無排版零件)\n`; continue; }
    for (const p of s.parts) {
      t += `\n零件：${p.name}  ${p.vertices.length} 頂點　面積 ${p.areaM2} m²${p.curved ? '　(含弧線)' : ''}\n`;
      p.vertices.forEach((v, i) => { t += `  V${i + 1}: (${v.x.toFixed(2)}, ${v.y.toFixed(2)})\n`; });
      if (p.curved) t += `  切割輪廓(取樣 ${p.outline.length} 點): ${p.outline.map(o => `(${o.x},${o.y})`).join(' ')}\n`;
    }
  }
  if (d.unplaced.length) t += `\n未排版(不在石材上)：${d.unplaced.join('、')}\n`;
  return t;
}
function exportToCsv(d) {
  const rows = ['slab,part,vertex,x_cm,y_cm'];
  for (const s of d.slabs) for (const p of s.parts) p.vertices.forEach((v, i) => rows.push(`${s.name},${p.name},${i + 1},${v.x},${v.y}`));
  return rows.join('\n');
}
function downloadFile(name, text, type) {
  const a = document.createElement('a');
  a.href = URL.createObjectURL(new Blob([text], { type }));
  a.download = name; a.click();
}
function openExport() {
  if (!State.slabs.length) return setStatus('尚未匯入石材，無法輸出座標。');
  exportData = buildExport();
  $('exportText').value = exportToText(exportData);
  $('exportDialog').hidden = false;
  setStatus('已產生切版座標，可複製或下載。');
}
$('exportBtn').addEventListener('click', openExport);
$('exClose').addEventListener('click', () => { $('exportDialog').hidden = true; });
$('exCopy').addEventListener('click', () => {
  const ta = $('exportText'); ta.select();
  try { navigator.clipboard.writeText(ta.value); } catch (e) { document.execCommand('copy'); }
  setStatus('座標已複製到剪貼簿。');
});
$('exTxt').addEventListener('click', () => downloadFile('stone-coords.txt', $('exportText').value, 'text/plain'));
$('exCsv').addEventListener('click', () => downloadFile('stone-coords.csv', exportToCsv(exportData), 'text/csv'));
$('exJson').addEventListener('click', () => downloadFile('stone-coords.json', JSON.stringify(exportData, null, 2), 'application/json'));

$('loadInput').addEventListener('change', (e) => {
  const file = e.target.files[0]; if (!file) return;
  const reader = new FileReader();
  reader.onload = () => { try { loadProject(JSON.parse(reader.result)); } catch (err) { setStatus('讀檔失敗：' + err.message); } };
  reader.readAsText(file); e.target.value = '';
});

function loadProject(data) {
  resetAll(true);
  let pending = data.slabs.length;
  if (!pending) { finishLoad(data); return; }
  data.slabs.forEach(sd => {
    addSlabFromSrc(sd.src, sd.name, sd.widthIn, sd.heightIn, (slab) => {
      slab.id = sd.id;                   // 還原原始 id 以對應 part.slabId
      slabStore[sd.id] = { src: sd.src, img: slab.img };
      if (--pending === 0) finishLoad(data);
    });
  });
}
function finishLoad(data) {
  for (const pd of data.parts) {
    makePart({
      name: pd.name, verts: pd.verts, thickIn: pd.thickIn, elevIn: pd.elevIn,
      vertical: pd.vertical, rot2d: pd.rot2d, layoutX: pd.layoutX, layoutY: pd.layoutY,
      pos3d: pd.pos3d, rotY: pd.rotY, tiltX: pd.tiltX || 0, tiltZ: pd.tiltZ || 0, select: false,
    });
    const p = State.parts[State.parts.length - 1];
    p.slabId = pd.slabId; applyPartTexture(p); updatePartTransform(p);
  }
  State.nextId = data.nextId || State.nextId;
  State.view2d.fitted = false;
  rebuild2DLayout(); updatePropPanel();
  clearHistory();
  setStatus('專案已載入。');
}

/* ===================================================================
   按鈕 / 鍵盤
   =================================================================== */
$('addPartBtn').addEventListener('click', () => startPlace('rect'));
$('addTriBtn').addEventListener('click', () => startPlace('tri'));
$('polyBtn').addEventListener('click', toggleDrawMode);
$('rotate2dBtn').addEventListener('click', (e) => rotate2d(e.shiftKey));
$('moveBtn').addEventListener('click', () => setGizmoMode('move'));
$('rot3dBtn').addEventListener('click', () => setGizmoMode('rotate'));
$('rotReset').addEventListener('click', resetRot3D);
$('snapBtn').addEventListener('click', doSnap);
$('orientBtn').addEventListener('click', armEdgeOrient);
$('standEdgeBtn').addEventListener('click', armStandEdge);
$('deleteBtn').addEventListener('click', deleteSelected);
$('resetBtn').addEventListener('click', () => { if (State.parts.length || State.slabs.length) pushSnap(snapshot()); resetAll(); });
$('saveBtn').addEventListener('click', saveProject);
$('undoBtn').addEventListener('click', doUndo);
$('redoBtn').addEventListener('click', doRedo);
$('fitBtn').addEventListener('click', () => { State.view2d.fitted = false; rebuild2DLayout(); });
$('gridBtn').addEventListener('click', () => {
  State.snapOn = !State.snapOn;
  $('gridBtn').textContent = `▦ 格線：${State.snapOn ? '開' : '關'}`;
  $('gridBtn').classList.toggle('active', State.snapOn);
  draw2D();
});
$('bgDarkBtn').addEventListener('click', () => setBackground('dark'));
$('bgLightBtn').addEventListener('click', () => setBackground('light'));
$('finishPolyBtn').addEventListener('click', finishPolygon);
$('cancelPolyBtn').addEventListener('click', cancelDraw);
$('nodeBtn').addEventListener('click', toggleNodeEdit);

function enterNodeEdit(id) {
  clearGizmoMode();
  selectPart(id); State.nodeEdit = id;
  $('nodeBtn').classList.add('active'); draw2D();
  setStatus('節點編輯：拖節點=移動、拖控制桿=調曲率方向、Alt 拖控制桿=拆成獨立方向(尖角)、Alt 拖節點=從角點拉出控制桿。Esc 離開。');
}
function exitNodeEdit() { State.nodeEdit = null; $('nodeBtn').classList.remove('active'); draw2D(); setStatus('已離開節點編輯。'); }
function toggleNodeEdit() {
  if (State.nodeEdit) exitNodeEdit();
  else if (State.selectedId != null) enterNodeEdit(State.selectedId);
  else setStatus('請先選一個零件，再進入節點編輯。');
}

window.addEventListener('keydown', (e) => {
  if (e.target.tagName === 'INPUT') return;
  if ((e.ctrlKey || e.metaKey) && (e.key === 'z' || e.key === 'Z')) { e.preventDefault(); e.shiftKey ? doRedo() : doUndo(); return; }
  if ((e.ctrlKey || e.metaKey) && (e.key === 'y' || e.key === 'Y')) { e.preventDefault(); doRedo(); return; }
  if (e.key === 'Escape') { if (State.drawMode) cancelDraw(); if (State.placeMode) cancelPlace(); if (State.nodeEdit) exitNodeEdit(); if (State.standPick) { State.standPick = false; $('standEdgeBtn').classList.remove('armed'); setStatus('已取消立起。'); } if (State.edgeOrient) { State.edgeOrient = null; $('orientBtn').classList.remove('armed'); clearEdgeHL(); setStatus('已取消邊線接合。'); } return; }
  if (e.key === 'Enter' && State.drawMode) { finishPolygon(); return; }
  switch (e.key.toLowerCase()) {
    case 'r': rotate2d(e.shiftKey); break;
    case 'a': doSnap(); break;
    case 'o': armEdgeOrient(); break;
    case 'delete': case 'backspace': deleteSelected(); break;
  }
});

function resetAll(silent) {
  clearEdgeHL();
  for (const p of State.parts) { scene.remove(p.group); disposeGroup(p.group); }
  State.parts = []; State.slabs = []; State.selectedId = null; State.nextId = 1;
  State.drawMode = null; State.edgeOrient = null; State.nodeEdit = null; State.placeMode = null; State.placeDrag = null; State.standPick = false;
  $('polyBtn').classList.remove('armed'); $('orientBtn').classList.remove('armed'); $('nodeBtn').classList.remove('active'); $('drawToolbar').hidden = true;
  $('addPartBtn').classList.remove('armed'); $('addTriBtn').classList.remove('armed'); $('standEdgeBtn').classList.remove('armed');
  clearGizmoMode();
  State.view2d.fitted = false;
  renderSlabList(); rebuild2DLayout(); updatePropPanel();
  if (!silent) setStatus('已重置。');
}

/* ===================================================================
   啟動
   =================================================================== */
/* ===================================================================
   Undo / Redo 歷史
   =================================================================== */
const slabStore = {};                 // id → {src, img}：整個 session 保留石材圖片
const History = { undo: [], redo: [], limit: 100 };
let dragStartSnap = null;

function snapshot() {
  return JSON.stringify({
    nextId: State.nextId,
    selectedId: State.selectedId,
    slabs: State.slabs.map(s => ({ id: s.id, name: s.name, widthIn: s.widthIn, heightIn: s.heightIn })),
    parts: State.parts.map(p => ({
      id: p.id, name: p.name, verts: p.verts, thickIn: p.thickIn, elevIn: p.elevIn,
      vertical: p.vertical, rot2d: p.rot2d, slabId: p.slabId, layoutX: p.layoutX, layoutY: p.layoutY,
      pos3d: p.pos3d, rotY: p.rotY, tiltX: p.tiltX || 0, tiltZ: p.tiltZ || 0,
    })),
  });
}
function pushSnap(s) {
  History.undo.push(s);
  if (History.undo.length > History.limit) History.undo.shift();
  History.redo.length = 0;
}
function beginDrag() { dragStartSnap = snapshot(); }
function commitDrag() {
  if (dragStartSnap != null) { if (dragStartSnap !== snapshot()) pushSnap(dragStartSnap); dragStartSnap = null; }
}
function clearHistory() { History.undo.length = 0; History.redo.length = 0; }

function addPartFromData(pd) {
  const part = {
    id: pd.id, name: pd.name, verts: pd.verts.map(v => ({ ...v })),
    thickIn: pd.thickIn, elevIn: pd.elevIn, vertical: pd.vertical, rot2d: pd.rot2d,
    slabId: pd.slabId, layoutX: pd.layoutX, layoutY: pd.layoutY,
    pos3d: { x: pd.pos3d.x, z: pd.pos3d.z }, rotY: pd.rotY, tiltX: pd.tiltX || 0, tiltZ: pd.tiltZ || 0,
    group: null, inner: null, body: null, topSkin: null, botSkin: null, outline: null,
  };
  State.parts.push(part);
  buildPartMesh(part);
  return part;
}

function restore(json) {
  const data = JSON.parse(json);
  // 取消進行中模式
  clearEdgeHL(); clearGizmoMode();
  State.drawMode = null; State.edgeOrient = null; State.nodeEdit = null; State.placeMode = null; State.placeDrag = null; State.standPick = false;
  $('polyBtn').classList.remove('armed'); $('orientBtn').classList.remove('armed');
  $('nodeBtn').classList.remove('active'); $('drawToolbar').hidden = true;
  $('addPartBtn').classList.remove('armed'); $('addTriBtn').classList.remove('armed'); $('standEdgeBtn').classList.remove('armed');
  // 清掉現有 3D
  for (const p of State.parts) { scene.remove(p.group); disposeGroup(p.group); }
  State.parts = [];
  // 還原石材（圖片取自 session 快取）
  State.slabs = data.slabs.map(sd => {
    const st = slabStore[sd.id] || {};
    return { id: sd.id, name: sd.name, widthIn: sd.widthIn, heightIn: sd.heightIn, src: st.src || '', img: st.img || null, originX: 0, originY: 0, tex: null };
  });
  // 還原零件
  for (const pd of data.parts) addPartFromData(pd);
  State.nextId = data.nextId;
  renderSlabList();
  rebuild2DLayout();
  selectPart(getPart(data.selectedId) ? data.selectedId : null);
}

function doUndo() {
  if (!History.undo.length) { setStatus('沒有可復原的步驟。'); return; }
  History.redo.push(snapshot());
  restore(History.undo.pop());
  setStatus(`已復原 (Undo)。可重做 ${History.redo.length} 步。`);
}
function doRedo() {
  if (!History.redo.length) { setStatus('沒有可重做的步驟。'); return; }
  History.undo.push(snapshot());
  restore(History.redo.pop());
  setStatus(`已重做 (Redo)。`);
}

function setupSplitter() {
  const sp = $('splitter'), left = $('leftCol'), ws = $('workspace');
  let dragging = false;
  sp.addEventListener('pointerdown', (e) => {
    dragging = true; sp.classList.add('dragging'); sp.setPointerCapture(e.pointerId);
    e.preventDefault();
  });
  sp.addEventListener('pointermove', (e) => {
    if (!dragging) return;
    const rail = $('toolrail').getBoundingClientRect();
    const wsRect = ws.getBoundingClientRect();
    let w = e.clientX - rail.right;                         // 左欄寬 = 游標到工具列右緣
    const max = wsRect.right - rail.right - 300;            // 右側至少留 300px
    w = Math.max(300, Math.min(w, max));
    left.style.width = w + 'px';
    onResize();
  });
  const end = () => { dragging = false; sp.classList.remove('dragging'); };
  sp.addEventListener('pointerup', end);
  sp.addEventListener('pointercancel', end);
}

init3D();
setupSplitter();
bindPropInputs();
renderSlabList();
rebuild2DLayout();
updatePropPanel();
setBackground('dark');
setStatus('① 匯入兩張石材 ② 新增/繪製零件 ③ 拖到石材上即時貼圖 ④ 右側 V 立起、O 邊線接合 組裝 3D。滾輪縮放、空白拖曳平移。');
setTimeout(onResize, 50);
