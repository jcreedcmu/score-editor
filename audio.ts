import { Score } from './types';

export const ad = new AudioContext();
const RATE = ad.sampleRate; // most likely 44100, maybe 48000?
// units: audio frames per second

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

const noise = [];
for (var i = 0; i < 10000; i++) {
  noise[i] = Math.random() - 0.5;
}

function audio_render_notes(ad, score: Score, progress: (t: number) => void) {
  const segmentTime = score.duration * score.seconds_per_tick;
  const len = segmentTime * RATE; // in frames
  var buf = ad.createBuffer(1, len, RATE);
  var dat = buf.getChannelData(0);
  for (const pu of score.song) {
	 const pu_frame_offset = pu.start * score.seconds_per_tick * RATE;
	 const pat = score.patterns[pu.patName];
	 const inst = pu.patName == "drums" ? "drums" : "square";
	 // XXX ignoring pattern *use* duration?
	 pat.notes.forEach(note => {
		const {env_f, real_length} = adsr(global_adsr_params,
													 (note.time[1] - note.time[0]) * score.seconds_per_tick);
		const note_start_frame = Math.round(note.time[0] * score.seconds_per_tick * RATE);
		const note_term_frame = Math.round(note.time[0] * score.seconds_per_tick * RATE + real_length * RATE);
		const state = {phase: 0, amp: 1, f: freq_of_pitch(note.pitch)};

		if (inst == "drums") {
		  for (var t = note_start_frame; t < note_term_frame; t++) {
			 state.phase += 100 * state.f / RATE;
			 let e = env_f((t - note_start_frame) / RATE);
			 const wav = 0.3 * noise[Math.floor(state.phase) % 10000];
			 dat[t] += e * state.amp * wav * (1 - (t - note_start_frame) / (note_term_frame - note_start_frame)) ;
		  }
		}
		else if (inst == "square") {
		  for (var t = note_start_frame; t < note_term_frame; t++) {
			 state.phase += state.f / RATE;
			 let e = env_f((t - note_start_frame) / RATE);
			 //const wav = 0.15 * Math.sin(3.1415926535 * 2 * state.phase);
			 const wav = 0.05 * ((state.phase - Math.floor(state.phase) < 0.5) ? 1 : -1);
			 dat[pu_frame_offset + t] += e * state.amp * wav ;
		  }
		}
	 });

  }

  var src = ad.createBufferSource();

  const beginTime = ad.currentTime + 0.1;

  const ival = setInterval(() => {
	 if (ad.currentTime < beginTime)
		return;
	 progress((ad.currentTime - beginTime) / score.seconds_per_tick);
  }, 40);

  src.onended = () => {
	 progress(null);
	 clearInterval(ival);
  }
  src.buffer = buf;
  src.connect(ad.destination);
  src.start(beginTime);
}

type NoteState = {
  phase: number,
  freq: number,
}

type AudioState = {
  nextUpdateTimeout? : number,
  renderedUntil?: number, // seconds
  renderedUntilSong? : number, // ticks
  liveNotes: NoteState[],
}

const state : AudioState = {
  liveNotes: [],
};

const COAST_MARGIN = 0.1; // seconds
const WARMUP_TIME = 0.05; // seconds
const UPDATE_INTERVAL = 0.025; // seconds
const RENDER_CHUNK_SIZE = 4096; // frames

export function play(score: Score, progress: (x: number, y: number) => void) {

  function coast(now: number, renderedUntil?: number) {
	 return renderedUntil != undefined && renderedUntil - now > COAST_MARGIN;
  }

  function audioUpdate() {
	 const now = ad.currentTime;

	 // points in time:
	 // N = present
    // B = program begin
	 // R = renderpoint
	 // S = song begin
	 // 'now' is (N - B) seconds
	 // renderedUntilSong is (R - S) ticks
	 // renderedUntil is (R - B) seconds
	 // cursor is: (N - S) ticks
	 const nowTicks = now / score.seconds_per_tick;
	 const ruTicks = state.renderedUntil / score.seconds_per_tick;
	 const cursor = nowTicks + state.renderedUntilSong - ruTicks;

	 // do we need to render?
	 if (state.renderedUntilSong < score.duration &&
		  (state.renderedUntil - now) < COAST_MARGIN) {
		const render_chunk_size_seconds = RENDER_CHUNK_SIZE / RATE;
		const render_chunk_size_ticks = render_chunk_size_seconds / score.seconds_per_tick;
		const buf = ad.createBuffer(1 /* channel */, RENDER_CHUNK_SIZE, RATE);
		const dat: Float32Array = buf.getChannelData(0);
		for (let i = 0; i < RENDER_CHUNK_SIZE; i++) {
		  dat[i] = i % 256 == 0 ? 0.01 : -0.01;
		}

		const src = ad.createBufferSource();
		src.buffer = buf;
		src.connect(ad.destination);
		console.log(state.renderedUntil * RATE);
		src.start(state.renderedUntil);

		state.renderedUntil += render_chunk_size_seconds;
		state.renderedUntilSong += render_chunk_size_ticks;
	 }

	 if (cursor > score.duration) {
		progress(undefined, undefined);
		return;
	 }
	 progress(cursor, state.renderedUntilSong);
	 state.nextUpdateTimeout = setTimeout(audioUpdate, UPDATE_INTERVAL * 1000);
  }

  state.renderedUntilSong = 0;
  state.renderedUntil = ad.currentTime + WARMUP_TIME;
  state.nextUpdateTimeout = setTimeout(audioUpdate, 0);
}
