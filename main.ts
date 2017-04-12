const c = document.getElementById('c') as HTMLCanvasElement;
const d = c.getContext('2d');
const w = innerWidth;
const h = innerHeight;

const oldWidth = w;
const oldHeight = h;
const ratio = devicePixelRatio;

c.width = oldWidth;
c.height = oldHeight;

c.width = oldWidth * ratio;
c.height = oldHeight * ratio;

c.style.width = oldWidth + 'px';
c.style.height = oldHeight + 'px';

d.imageSmoothingEnabled = false;
d.webkitImageSmoothingEnabled = false;

const SCALE = 2;
const PIANO_H = 73;
const PIANO_W = 43;
const PIANO_OCTAVE_VSPACE = (PIANO_H - 1) * SCALE;
const PIANO_WIDTH = (PIANO_W) * SCALE;

function box(d, x, y, w, h, border, c, bc) {
  d.fillStyle = bc;
  d.fillRect(x * SCALE, y * SCALE, w * SCALE, h * SCALE);
  d.fillStyle = c;
  d.fillRect((x + border) * SCALE, (y + border) * SCALE, (w - 2*border) * SCALE, (h-2*border) * SCALE);
}

const colors = [
  "#7882e2",
  "#38396e",
  "#df4f48",
  "#696800",
  "#fffd58",
  "#f47937",
  "#782a00",
  "#71d256",
  "#790061",
  "#d343b6",
  "#075152",
  "#75c4c5",
];

function octave(d, x, y) {
  d.save();
  d.translate(x, y);
  box(d, 0, 0, PIANO_W, PIANO_H, 1, "#f8f8d8", "black");
  d.fillStyle = "black";
  [10, 21, 32, 42, 52, 62].forEach(wks =>
											  d.fillRect(0, wks * SCALE, PIANO_W * SCALE, 1 * SCALE)
											 );
  [1, 3, 5, 8, 10].forEach(bk =>
									box(d, 0, 6 * bk, 25, 7, 1, "#2e2234", "black")
								  );

  d.restore();
}

function staff_octave(d, x, y, w) {
  d.fillStyle = "black";
  d.save();
  d.translate(x, y);
  d.fillRect(0, 0, w * SCALE, PIANO_H * SCALE);
  const colors = [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0];
  for (let n = 0; n < 12; n++) {
	 d.fillStyle = colors[n] ? "#141414" : "#262626";
	 d.fillRect(SCALE, (6 * n + 1) * SCALE, (w-2) * SCALE, 5 * SCALE);
  }
  d.restore();
}

for (let oc = 0; oc < 3; oc++) {
  octave(d, 100, 100 + oc * PIANO_OCTAVE_VSPACE);
  staff_octave(d, 100 + PIANO_WIDTH + SCALE, 100 + oc * PIANO_OCTAVE_VSPACE, 250);
}
