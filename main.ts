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

const keytype = [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0];


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
  for (let n = 0; n < 12; n++) {
	 d.fillStyle = keytype[n] ? "#141414" : "#262626";
	 d.fillRect(SCALE, (6 * n + 1) * SCALE, (w-2) * SCALE, 5 * SCALE);
  }
  d.restore();
}

// I find this just helps guide my eye
function gutter(d, x, y, w) {
  d.fillStyle = "black";
  d.save();
  d.translate(x, y);
  box(d, 0, 0, w, PIANO_H, 1, "#262626", "black")

  for (let n = 0; n < 12; n++) {
	 if (keytype[n]) {
		box(d, w - 7, 6 * n, 5, 7, 1, "#141414", "black");
	 }
  }

  d.restore();
}

const GUTTER_W = 8;
const GUTTER_WIDTH = GUTTER_W * SCALE;

for (let oc = 0; oc < 3; oc++) {
  octave(d, 100, 100 + oc * PIANO_OCTAVE_VSPACE);
  gutter(d, 100 + PIANO_WIDTH + SCALE, 100 + oc * PIANO_OCTAVE_VSPACE, 10);
  staff_octave(d, 100 + PIANO_WIDTH + GUTTER_WIDTH, 100 + oc * PIANO_OCTAVE_VSPACE, 250);
}

// got these from 'overboard'
// https://twitter.com/jcreed/status/851457146852184065
// beepbox export to json then
// jq -c '[.channels[0,1,2].patterns[1].notes[]|{pitch:.pitches[0], time: [.points[0].tick, .points[1].tick]}]'  /tmp/BeepBox-Song.json
const notes = [{"pitch":50,"time":[0,4]},{"pitch":54,"time":[4,8]},{"pitch":54,"time":[8,12]},{"pitch":52,"time":[12,16]},{"pitch":50,"time":[16,24]},{"pitch":50,"time":[28,32]},{"pitch":42,"time":[0,4]},{"pitch":45,"time":[4,8]},{"pitch":45,"time":[8,12]},{"pitch":43,"time":[12,16]},{"pitch":42,"time":[16,20]},{"pitch":43,"time":[20,24]},{"pitch":45,"time":[24,26]},{"pitch":43,"time":[26,28]},{"pitch":42,"time":[28,32]},{"pitch":26,"time":[0,4]},{"pitch":23,"time":[16,20]}];

notes.forEach(note => note.pitch += 3);

function render_notes(d, notes, x, y, pitch_at_y0, ticks_at_x0, fat_pixels_per_tick) {
  d.save();
  d.translate(x, y);
  notes.forEach(note => {
	 const nx = (note.time[0] - ticks_at_x0) * fat_pixels_per_tick;
	 const nw = (note.time[1] - note.time[0]) * fat_pixels_per_tick + 1;
	 const ny = (pitch_at_y0 - note.pitch) * 6;
	 const nh = 7;
	 box(d, nx, ny, nw, nh, 1, colors[note.pitch % 12], "black")
  });
  d.restore();
}

render_notes(d, notes, 100 + PIANO_WIDTH + GUTTER_WIDTH, 100,
				 -1 + 12 * 5, 0, 6);
