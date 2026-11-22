// Sokoban solver: push-optimal per-room A*.
// Levels are a 1-wide hallway with 1-4 rooms off it; a box that leaves its room
// can never come back, so each room is solved on its own (push-optimal A* with
// deadlock pruning and a min-cost-assignment heuristic) and the room solutions
// are joined by walking the player through the hallway. Node 22, stdlib only,
// no clock, no network, deterministic: fixed iteration order and node budgets.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const DL = ['u', 'd', 'l', 'r'];

// ---------------- parsing ----------------
function parseLevel(text) {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals = [];
  const boxes = [];
  let player = -1;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const ch = rows[y][x] ?? '#';
      if (ch === '#') continue;
      const i = y * w + x;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  }
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player, hallwayRow: Math.floor(player / w) };
}

// ---------------- room decomposition ----------------
// Rooms are the connected floor regions off the hallway row (the row the player
// starts on). Each holds its own boxes and goals; nothing else can enter it.
function findRooms(lv) {
  const { w, h, wall, boxes, goals, hallwayRow } = lv;
  const comp = new Int32Array(w * h).fill(-1);
  const comps = [];
  for (let i = 0; i < w * h; i++) {
    if (wall[i] || Math.floor(i / w) === hallwayRow || comp[i] >= 0) continue;
    const cells = [];
    const q = [i];
    comp[i] = comps.length;
    let head = 0;
    while (head < q.length) {
      const c = q[head++];
      cells.push(c);
      const x = c % w, y = (c / w) | 0;
      for (let d = 0; d < 4; d++) {
        const nx = x + DX[d], ny = y + DY[d];
        if (nx < 0 || nx >= w || ny < 0 || ny >= h) continue;
        const n = ny * w + nx;
        if (!wall[n] && Math.floor(n / w) !== hallwayRow && comp[n] < 0) {
          comp[n] = comps.length;
          q.push(n);
        }
      }
    }
    comps.push(cells);
  }
  const rooms = [];
  for (const cells of comps) {
    const set = new Uint8Array(w * h);
    for (const c of cells) set[c] = 1;
    const rb = boxes.filter((b) => set[b]);
    const rg = goals.filter((g) => set[g]);
    if (rb.length === 0) continue;
    rooms.push({ cells, set, boxes: rb, goals: rg });
  }
  return rooms;
}

// ---------------- per-room tables ----------------
// live[c]: a box on c can still reach a goal (reverse-pull reachability from
// the goals). A box off the live set is dead and its state is pruned.
// dists[g][c]: shortest box-push path from c to goal g over the room's floor.
function prepRoom(lv, room) {
  const { w, h, wall } = lv;
  const N = w * h;
  // Reverse-pull reachability from the goals: a box on s can be pushed to a
  // live square t = s + d only if the player can stand at s - d = t - 2d, so
  // s is live when that player cell is free floor. (Checking t + d instead
  // marks truly-live squares dead, e.g. a box under a goal with a wall
  // above the goal, and the search then prunes every successor.)
  const live = new Uint8Array(N);
  const q = [];
  for (const g of room.goals) {
    if (!live[g]) { live[g] = 1; q.push(g); }
  }
  let head = 0;
  while (head < q.length) {
    const t = q[head++];
    const tx = t % w, ty = (t / w) | 0;
    for (let d = 0; d < 4; d++) {
      const sx = tx - DX[d], sy = ty - DY[d];
      const bx = tx - 2 * DX[d], by = ty - 2 * DY[d];
      if (sx < 0 || sx >= w || sy < 0 || sy >= h) continue;
      if (bx < 0 || bx >= w || by < 0 || by >= h) continue;
      const s = sy * w + sx, b = by * w + bx;
      if (!room.set[s] || wall[b] || live[s]) continue;
      live[s] = 1;
      q.push(s);
    }
  }
  const dists = [];
  for (const g of room.goals) {
    const dist = new Int32Array(N).fill(-1);
    dist[g] = 0;
    const qq = [g];
    let hh = 0;
    while (hh < qq.length) {
      const c = qq[hh++];
      const cx = c % w, cy = (c / w) | 0;
      for (let d = 0; d < 4; d++) {
        const nx = cx + DX[d], ny = cy + DY[d];
        if (nx < 0 || nx >= w || ny < 0 || ny >= h) continue;
        const n = ny * w + nx;
        if (!room.set[n] || dist[n] >= 0) continue;
        dist[n] = dist[c] + 1;
        qq.push(n);
      }
    }
    dists.push(dist);
  }
  room.live = live;
  room.dists = dists;
  room.goalSet = new Set(room.goals);
}

// ---------------- per-room push-optimal A* ----------------
// State: sorted room-box cells + the player's canonical cell (the lowest cell
// of the free-space component the player stands in). Cost is pushes; the
// heuristic is the min-cost assignment of boxes to goals by push distance.
// Dead-square and freeze pruning keep the search small. gw/hw weight the
// priority (1,1) optimal, (1,2) weighted, (0,1) greedy fallback.
function solveRoom(lv, room, blocked, startBoxes, startPlayer, requireExit, maxExp, gw, hw) {
  const { w, h } = lv;
  const N = w * h;
  const n = startBoxes.length;
  const dists = room.dists;
  const live = room.live;
  const goalSet = room.goalSet;
  const hallwayRow = lv.hallwayRow;

  const vis = new Int32Array(N);
  let stamp = 0;
  // Flood from `from` over cells that are neither blocked nor a box in
  // `boxes`. Returns [lowest cell of the component, does it touch the hall].
  function flood(from, boxes) {
    stamp++;
    const q = [from];
    vis[from] = stamp;
    let min = Infinity;
    let hasHall = false;
    let head = 0;
    while (head < q.length) {
      const c = q[head++];
      if (c < min) min = c;
      if (Math.floor(c / w) === hallwayRow) hasHall = true;
      const x = c % w, y = (c / w) | 0;
      for (let d = 0; d < 4; d++) {
        const nx = x + DX[d], ny = y + DY[d];
        if (nx < 0 || nx >= w || ny < 0 || ny >= h) continue;
        const nn = ny * w + nx;
        if (blocked[nn] || vis[nn] === stamp) continue;
        let isBox = false;
        for (let k = 0; k < boxes.length; k++) {
          if (boxes[k] === nn) { isBox = true; break; }
        }
        if (isBox) continue;
        vis[nn] = stamp;
        q.push(nn);
      }
    }
    return [min, hasHall];
  }
  function inReach(c) { return vis[c] === stamp; }

  function heur(boxes) {
    let bestH = Infinity;
    const used = new Array(n).fill(false);
    (function rec(i, sum) {
      if (sum >= bestH) return;
      if (i === n) { bestH = sum; return; }
      for (let g = 0; g < n; g++) {
        if (used[g]) continue;
        const d = dists[g][boxes[i]];
        if (d < 0) continue;
        used[g] = true;
        rec(i + 1, sum + d);
        used[g] = false;
      }
    })(0, 0);
    return bestH;
  }

  function deadBoxes(boxes) {
    for (let i = 0; i < boxes.length; i++) {
      if (!live[boxes[i]]) return true;
    }
    return false;
  }

  // A box is frozen when no push is possible even if every unfrozen box moved
  // away. A frozen box off a goal makes the state dead.
  function freezeDead(boxes) {
    const frozen = new Set();
    let changed = true;
    while (changed) {
      changed = false;
      for (let i = 0; i < boxes.length; i++) {
        const b = boxes[i];
        if (frozen.has(b)) continue;
        let canMove = false;
        const bx = b % w, by = (b / w) | 0;
        for (let d = 0; d < 4; d++) {
          const tx = bx + DX[d], ty = by + DY[d];
          const px = bx - DX[d], py = by - DY[d];
          if (tx < 0 || tx >= w || ty < 0 || ty >= h) continue;
          if (px < 0 || px >= w || py < 0 || py >= h) continue;
          const t = ty * w + tx, p = py * w + px;
          if (blocked[t] || frozen.has(t)) continue;
          if (blocked[p] || frozen.has(p)) continue;
          canMove = true;
          break;
        }
        if (!canMove) { frozen.add(b); changed = true; }
      }
    }
    for (const b of frozen) {
      if (!goalSet.has(b)) return true;
    }
    return false;
  }

  // Binary heap of [f, g, state index]; lower f, then higher g, then earlier.
  const heap = [];
  function cmp(a, b) {
    if (a[0] !== b[0]) return a[0] - b[0];
    if (a[1] !== b[1]) return b[1] - a[1];
    return a[2] - b[2];
  }
  function heapPush(e) {
    heap.push(e);
    let i = heap.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (cmp(heap[i], heap[p]) >= 0) break;
      const t = heap[i]; heap[i] = heap[p]; heap[p] = t;
      i = p;
    }
  }
  function heapPop() {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      let i = 0;
      for (;;) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && cmp(heap[c + 1], heap[c]) < 0) c++;
        if (cmp(heap[c], heap[i]) >= 0) break;
        const t = heap[i]; heap[i] = heap[c]; heap[c] = t;
        i = c;
      }
    }
    return top;
  }

  const sBoxes = [];
  const sPlayer = [];
  const sG = [];
  const sParent = [];
  const sPushBox = [];
  const sPushDir = [];
  const sKey = [];
  const best = new Map();
  const closed = new Set();

  const startSorted = [...startBoxes].sort((a, b) => a - b);
  const [startCanon] = flood(startPlayer, startSorted);
  const h0 = heur(startSorted);
  if (h0 === Infinity) return null;
  const key0 = startSorted.join(',') + ':' + startCanon;
  sBoxes.push(startSorted);
  sPlayer.push(startCanon);
  sG.push(0);
  sParent.push(-1);
  sPushBox.push(-1);
  sPushDir.push(-1);
  sKey.push(key0);
  best.set(key0, 0);
  heapPush([gw * 0 + hw * h0, 0, 0]);

  let expanded = 0;
  while (heap.length > 0) {
    const [, g, si] = heapPop();
    const key = sKey[si];
    if (closed.has(key)) continue;
    if (best.get(key) !== g) continue;
    closed.add(key);
    const boxes = sBoxes[si];
    const player = sPlayer[si];
    // Reachable set from this state (also tells us if the hall is reachable).
    const [, hasHall] = flood(player, boxes);
    let solved = true;
    for (let i = 0; i < boxes.length; i++) {
      if (!goalSet.has(boxes[i])) { solved = false; break; }
    }
    if (solved && (!requireExit || hasHall)) {
      const pushes = [];
      let t = si;
      while (t > 0) {
        pushes.push([sPushBox[t], sPushDir[t]]);
        t = sParent[t];
      }
      pushes.reverse();
      return { pushes, canExit: hasHall, expansions: expanded };
    }
    if (expanded >= maxExp) return null;
    expanded++;
    // Collect the pushes the player can make from this reachable set first,
    // because the successor flood below overwrites the stamp.
    const valid = [];
    for (let bi = 0; bi < boxes.length; bi++) {
      const b = boxes[bi];
      const bx = b % w, by = (b / w) | 0;
      for (let d = 0; d < 4; d++) {
        const px = bx - DX[d], py = by - DY[d];
        const tx = bx + DX[d], ty = by + DY[d];
        if (px < 0 || px >= w || py < 0 || py >= h) continue;
        if (tx < 0 || tx >= w || ty < 0 || ty >= h) continue;
        const p = py * w + px, t = ty * w + tx;
        if (!inReach(p)) continue;
        if (blocked[t]) continue;
        let tIsBox = false;
        for (let k = 0; k < boxes.length; k++) {
          if (boxes[k] === t) { tIsBox = true; break; }
        }
        if (tIsBox) continue;
        valid.push([bi, d, t]);
      }
    }
    for (const [bi, d, t] of valid) {
      const nb = boxes.slice();
      nb[bi] = t;
      nb.sort((a, b) => a - b);
      if (deadBoxes(nb)) continue;
      if (freezeDead(nb)) continue;
      const hh = heur(nb);
      if (hh === Infinity) continue;
      const [newCanon] = flood(boxes[bi], nb);
      const ng = g + 1;
      const nkey = nb.join(',') + ':' + newCanon;
      const prevBest = best.get(nkey);
      if (prevBest !== undefined && prevBest <= ng) continue;
      best.set(nkey, ng);
      const ni = sBoxes.length;
      sBoxes.push(nb);
      sPlayer.push(newCanon);
      sG.push(ng);
      sParent.push(si);
      sPushBox.push(boxes[bi]);
      sPushDir.push(d);
      sKey.push(nkey);
      heapPush([gw * ng + hw * hh, ng, ni]);
    }
  }
  return null;
}

// Try optimal A*, then weighted, then greedy. Returns null when unsolved.
function solveRoomTries(lv, room, blocked, startBoxes, startPlayer, requireExit) {
  let r = solveRoom(lv, room, blocked, startBoxes, startPlayer, requireExit, 120000, 1, 1);
  if (r) return { ...r, mode: 'astar' };
  r = solveRoom(lv, room, blocked, startBoxes, startPlayer, requireExit, 200000, 1, 2);
  if (r) return { ...r, mode: 'weighted' };
  r = solveRoom(lv, room, blocked, startBoxes, startPlayer, requireExit, 200000, 0, 1);
  if (r) return { ...r, mode: 'greedy' };
  return null;
}

// ---------------- whole-level assembly ----------------
// Walk the player from `from` to `to` over cells that are neither walls nor
// boxes (boxes = current global boxes). Returns the move letters, or null.
function walkPath(lv, from, to, boxes) {
  const { w, h, wall } = lv;
  if (from === to) return '';
  const boxSet = new Set(boxes);
  const prev = new Int32Array(w * h).fill(-1);
  const prevDir = new Int8Array(w * h).fill(-1);
  const q = [from];
  prev[from] = from;
  let head = 0;
  while (head < q.length) {
    const c = q[head++];
    if (c === to) break;
    const x = c % w, y = (c / w) | 0;
    for (let d = 0; d < 4; d++) {
      const nx = x + DX[d], ny = y + DY[d];
      if (nx < 0 || nx >= w || ny < 0 || ny >= h) continue;
      const n = ny * w + nx;
      if (wall[n] || boxSet.has(n) || prev[n] >= 0) continue;
      prev[n] = c;
      prevDir[n] = d;
      q.push(n);
    }
  }
  if (prev[to] < 0) return null;
  let moves = '';
  let c = to;
  while (c !== from) {
    moves = DL[prevDir[c]] + moves;
    c = prev[c];
  }
  return moves;
}

function solveLevelText(text) {
  const lv = parseLevel(text);
  const rooms = findRooms(lv);
  // Sanity: every box in a room, boxes match goals per room.
  let totalBoxes = 0;
  for (const r of rooms) {
    totalBoxes += r.boxes.length;
    if (r.boxes.length !== r.goals.length) return '';
  }
  if (totalBoxes !== lv.boxes.length) return '';
  if (rooms.length === 0) return '';
  for (const r of rooms) prepRoom(lv, r);

  const { w, h, wall } = lv;
  const N = w * h;
  // Static obstacles per room: walls plus every other room's initial boxes.
  const roomBlocked = rooms.map((room, ri) => {
    const blocked = new Uint8Array(N);
    for (let i = 0; i < N; i++) blocked[i] = wall[i];
    for (let rj = 0; rj < rooms.length; rj++) {
      if (rj === ri) continue;
      for (const b of rooms[rj].boxes) blocked[b] = 1;
    }
    return blocked;
  });

  // Solve every room from the hallway, no exit requirement yet.
  const sols = [];
  for (let ri = 0; ri < rooms.length; ri++) {
    const s = solveRoomTries(lv, rooms[ri], roomBlocked[ri], rooms[ri].boxes, lv.player, false);
    if (!s) return '';
    sols.push(s);
  }
  // Rooms whose optimal solution strands the player inside must either be
  // solved with an exit or go last. Pick the last room to minimise pushes.
  const needExit = [];
  for (let ri = 0; ri < rooms.length; ri++) {
    if (!sols[ri].canExit) needExit.push(ri);
  }
  let order = rooms.map((_, i) => i);
  if (needExit.length > 0) {
    const withExit = new Map();
    for (const ri of needExit) {
      const s = solveRoomTries(lv, rooms[ri], roomBlocked[ri], rooms[ri].boxes, lv.player, true);
      if (!s) return '';
      withExit.set(ri, s);
    }
    // Total if room L is last: sum of with-exit pushes for the rest + b_L.
    let bestLast = -1;
    let bestTotal = Infinity;
    for (let L = 0; L < rooms.length; L++) {
      let total = 0;
      for (let ri = 0; ri < rooms.length; ri++) {
        if (ri === L) total += sols[ri].pushes.length;
        else total += (withExit.has(ri) ? withExit.get(ri) : sols[ri]).pushes.length;
      }
      if (total < bestTotal) { bestTotal = total; bestLast = L; }
    }
    for (let ri = 0; ri < rooms.length; ri++) {
      if (ri !== bestLast) sols[ri] = withExit.has(ri) ? withExit.get(ri) : sols[ri];
    }
    order = rooms.map((_, i) => i).filter((i) => i !== bestLast);
    order.push(bestLast);
  }

  // Reconstruct the full move string in the chosen room order.
  let boxes = [...lv.boxes];
  let player = lv.player;
  let moves = '';
  for (const ri of order) {
    for (const [box, d] of sols[ri].pushes) {
      const pushFrom = box - (DY[d] * w + DX[d]);
      const walk = walkPath(lv, player, pushFrom, boxes);
      if (walk === null) return '';
      moves += walk;
      moves += DL[d];
      const bi = boxes.indexOf(box);
      boxes[bi] = box + (DY[d] * w + DX[d]);
      player = box;
    }
  }
  // Verify: every box on a goal.
  const goalSet = new Set(lv.goals);
  for (const b of boxes) {
    if (!goalSet.has(b)) return '';
  }
  return moves;
}

for (const id of readdirSync(I).sort()) {
  const moves = solveLevelText(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), moves + '\n');
}
