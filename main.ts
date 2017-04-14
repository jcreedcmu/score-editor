export const ad = new AudioContext();
const RATE = ad.sampleRate; // most likely 44100, maybe 48000?

const c = document.getElementById('c') as HTMLCanvasElement;
const c2 = document.getElementById('c2') as HTMLCanvasElement;
const d = c.getContext('2d');
const d2 = c2.getContext('2d');
const w = innerWidth;
const h = innerHeight;

declare const debug_glob: any;

import { score } from './score';

function fullscreen(c, d) {
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
}
fullscreen(c, d);
fullscreen(c2, d2);

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
const SCORE_W = 250;
const SCORE_WIDTH = 250 * SCALE;

for (let oc = 0; oc < 3; oc++) {
  octave(d, 100, 100 + oc * PIANO_OCTAVE_VSPACE);
  gutter(d, 100 + PIANO_WIDTH + SCALE, 100 + oc * PIANO_OCTAVE_VSPACE, 10);
  staff_octave(d, 100 + PIANO_WIDTH + GUTTER_WIDTH, 100 + oc * PIANO_OCTAVE_VSPACE, 250);
}


const notes = score.notes;
notes.forEach(note => note.pitch += 12);

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

const FAT_PIXELS_PER_TICK = 6;
render_notes(d, notes, 100 + PIANO_WIDTH + GUTTER_WIDTH, 100,
				 -1 + 12 * 6, 0, FAT_PIXELS_PER_TICK);



function freq_of_pitch(pitch) {
  return 440 * Math.pow(2, (pitch - 69) / 12);
}

const global_adsr_params = {a: 0.01, d: 0.1, s: 0.5, r: 0.01};

function adsr(params, length) {
  const {a, d, s, r} = params;
  return {
	 env_f: (t => {
		if (t < a) { return t / a }
		if (t - a < d) { const T = (t - a) / d; return s * T + (1 - T); }
		if (t < length) return s;
		return s * (1 - (t - length) / r);
	 }),
	 real_length: length + r
  }
}


export function audio_render_notes(ad, score) {
  const segmentTime = score.duration * score.seconds_per_tick;
  const len = segmentTime * RATE; // in frames
  var buf = ad.createBuffer(1, len, RATE);
  var dat = buf.getChannelData(0);

  score.notes.forEach(note => {
	 const {env_f, real_length} = adsr(global_adsr_params,
												  (note.time[1] - note.time[0]) * score.seconds_per_tick);
	 const note_start_frame = Math.round(note.time[0] * score.seconds_per_tick * RATE);
	 const note_term_frame = Math.round(note.time[0] * score.seconds_per_tick * RATE + real_length * RATE);
	 const state = {phase: 0, amp: 1, f: freq_of_pitch(note.pitch)};

	 for (var t = note_start_frame; t < note_term_frame; t++) {
		state.phase += state.f / RATE;
		let e = env_f((t - note_start_frame) / RATE);
		const wav = 0.15 * Math.sin(3.1415926535 * 2 * state.phase);
//		const wav = 0.05 * ((state.phase - Math.floor(state.phase) < 0.5) ? 1 : -1);
		dat[t] += e * state.amp * wav ;
	 }
  });

  var src = ad.createBufferSource();

  const beginTime = ad.currentTime + 0.1;

  const ival = setInterval(() => {
	 if (ad.currentTime < beginTime)
		return;
	 d2.clearRect(0, 0, w, h);
	 d2.fillStyle = "white";
	 d2.fillRect(100 + PIANO_WIDTH + GUTTER_WIDTH + SCALE * FAT_PIXELS_PER_TICK / score.seconds_per_tick * (ad.currentTime - beginTime), 100,
					 2, PIANO_OCTAVE_VSPACE * 3);
  }, 40);

  src.onended = () => {
	 d2.clearRect(0, 0, w, h);
	 clearInterval(ival);
  }
  src.buffer = buf;
  src.connect(ad.destination);
  src.start(beginTime);
}


export function play() {
  audio_render_notes(ad, score);
}

window.onload = () => {
  document.getElementById('play').onclick = play;
}

// debugging
setTimeout(() => {
  window['score'] = score;
  for (let x in debug_glob) {
	 window[x] = debug_glob[x];
  }
}, 0);
