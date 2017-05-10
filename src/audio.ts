import { Score, IdNote, Progress } from './types';
import { dispatch } from './main';

export const ad = new AudioContext();
const RATE = ad.sampleRate; // most likely 44100, maybe 48000?
// units: audio frames per second

function freq_of_pitch(pitch) {
  return 440 * Math.pow(2, (pitch - 69) / 12);
}

const global_adsr_params = {a: 0.01, d: 0.1, s: 0.5, r: 0.01};

// a, d, r and length are all intended to be in seconds
// --- but the function would still work more or less the same for
// them being in any time unit, as long as they're all the same.
// s is a unitless scaling factor.
type adsrParams = {a: number, d: number, s: number, r: number};
function adsr(params: adsrParams, length: number) {
  const {a, d, s, r} = params;
  return  (t => {
	 let env;
	 if (t < a) env = t / a;
	 else if (t - a < d) {
		const T = (t - a) / d;
		env = s * T + (1 - T);
	 }
	 else {
		env = s;
	 }
	 const release_factor = (length - t) / r;
	 if (release_factor < 1) {
		env *= release_factor;
	 }
	 return env;
  });
}

const NOISE_LENGTH = 44100;
const noise = [];
for (var i = 0; i < NOISE_LENGTH; i++) {
  noise[i] = Math.random() - 0.5;
}

type NoteState = {
  id: string,
  pitch: number,
  phase: number,
  freq: number,
  buf: number,
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

type Instrument = "sine" | "drums"

// We want to keep two pieces of information that are both derived
// from the note's real time bounds
// (a) When the note starts and stops, considering it clipped to the
// render chunk
// (b) When the note actually begins and ends, which might be outside
// the render chunk, for purposes of computing adsr envelope.
type ClipNote = IdNote & {clipTime: [number, number], instrument: Instrument};

function repeats(patUseLength: number, patLength: number): {offset: number, duration: number}[] {
  let remaining: number = patUseLength;
  let pos = 0;
  let rv: {offset: number, duration: number}[] = [];
  while (remaining > patLength) {
	 rv.push({offset: pos, duration: patLength});
	 remaining -= patLength;
	 pos += patLength;
  }
  rv.push({offset: pos, duration: remaining});
  return rv;
}

function collectNotes(score: Score, start: number, duration: number): ClipNote[] {
  const rv: ClipNote[] = [];

  const ct = [start, start + duration]; // am I fenceposting wrong?
  for (const pu of score.song) {
	 const pu_offset = pu.start;
	 const pat = score.patterns[pu.patName];

	 repeats(pu.duration, pat.length).forEach(({offset, duration}) => {
		pat.notes.forEach(note => {
		  const off = offset + pu_offset;
		  const start = note.time[0];
		  if (start >= duration) return;
		  const end = Math.min(note.time[1], duration);
		  const nt: [number, number] = [off + start, off + end];
		  if (nt[0] <= ct[1] && ct[0] <= nt[1]) {
			 rv.push({...note,
						 id: note.id + "__" + pu.lane,
						 time: nt,
						 instrument: pu.patName == "drums" ? "drums" : "sine",
						 clipTime: [Math.max(nt[0], ct[0]), Math.min(nt[1], ct[1])]});
		  }
		});
	 });
  }
  return rv;
}

function clip_to_length(params: adsrParams, seconds: number): adsrParams {
  return {...params,
			 a: Math.min(params.a, seconds/2),
			 r: Math.min(params.r, seconds/2)};
}

function renderChunkInto(dat: Float32Array, startTicks: number, score: Score, liveNotes: NoteState[]): NoteState[] {

  const newLiveNotes = [];
  for (const note of collectNotes(score, startTicks, dat.length / (score.seconds_per_tick * RATE))) {
	 const noteState: NoteState = liveNotes.find(n => n.id == note.id) ||
		{id: note.id, phase: 0, pitch: note.pitch, freq: freq_of_pitch(note.pitch), buf: 0};
	 newLiveNotes.push(noteState);

	 const note_start_frame = Math.round((note.clipTime[0] - startTicks) * score.seconds_per_tick * RATE);
	 const note_term_frame = Math.round((note.clipTime[1] - startTicks) * score.seconds_per_tick * RATE);
	 const adsr_params = {...global_adsr_params};
	 if (note.instrument == "drums") {
		adsr_params.r = 0.0;
		adsr_params.a = 0.001;
		adsr_params.d = (note.time[1] - note.time[0]) * score.seconds_per_tick - adsr_params.a;
		adsr_params.s = 0.000;
	 }
	 const env_f = adsr(clip_to_length(adsr_params, (note.time[1] - note.time[0]) * score.seconds_per_tick),
							  (note.time[1] - note.time[0]) * score.seconds_per_tick);

	 switch (note.instrument) {
	 case "sine":
		for (let i = note_start_frame; i < note_term_frame; i++) {
		  // what time is it in this iteration of the loop? it's (in ticks from beginning of song)
		  // note.clipTime[0] + (i - note_start_frame) / (score.seconds_per_tick * RATE)

		  // therefore, the time in *seconds* since this note started is as follows:
		  const env = env_f((i - note_start_frame) / RATE + (note.clipTime[0] - note.time[0]) * score.seconds_per_tick);
		  noteState.phase += noteState.freq / RATE;
		  dat[i] += env * 0.15 * ((noteState.phase - Math.floor(noteState.phase)) < 0.5 ? 0.2 : -0.2);
		}
		break;
	 case "drums":
		const step = Math.pow(2, (note.pitch - 60) / 1.5);
		const p = Math.min(1.0, noteState.freq * 8.0 / RATE);
		const volumeAdjust = Math.pow(2.0, (50-note.pitch) / 12);
		for (let i = note_start_frame; i < note_term_frame; i++) {
		  const env = env_f((i - note_start_frame) / RATE + (note.clipTime[0] - note.time[0]) * score.seconds_per_tick);
		  noteState.phase += step;
		  if (noteState.phase >= NOISE_LENGTH) { noteState.phase -= NOISE_LENGTH; }
		  noteState.buf = (1-p) * noteState.buf + p * noise[Math.floor(noteState.phase)];
		  dat[i] += env * volumeAdjust * noteState.buf;
		}
		break;
	 }
  }
  return newLiveNotes;
}

function continuePlayback(score: Score): Progress {
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
	 state.liveNotes = renderChunkInto(dat, state.renderedUntilSong, score, state.liveNotes);

	 const src = ad.createBufferSource();
	 src.buffer = buf;
	 src.connect(ad.destination);

	 // I expect this to stay an integer (because audio context's
	 // "currentTime" seems to stay essentially an integer multiple of
	 // 1/RATE) although since I'm incrementing by floating point
	 // quantities of seconds, I observe it drifting by something on
	 // the order of 1e-8 seconds per second. Maybe could keep track of
	 // renderedUntilFrames as an integer instead. (no chance it'll get
	 // anywhere close to Number.MAX_SAFE_INTEGER in practice, I think)
	 // console.log(state.renderedUntil * RATE);

	 src.start(state.renderedUntil);

	 state.renderedUntil += render_chunk_size_seconds;
	 state.renderedUntilSong += render_chunk_size_ticks;
  }

  if (cursor > score.duration) {
	 return {v:undefined, dv:undefined};
  }
  state.nextUpdateTimeout = setTimeout(audioUpdate, UPDATE_INTERVAL * 1000);
  return {v: cursor, dv: state.renderedUntilSong};
}

export function play() {

  function coast(now: number, renderedUntil?: number) {
	 return renderedUntil != undefined && renderedUntil - now > COAST_MARGIN;
  }

  state.liveNotes = [];
  state.renderedUntilSong = 0;
  state.renderedUntil = ad.currentTime + WARMUP_TIME;
  state.nextUpdateTimeout = setTimeout(audioUpdate, 0);
}

function audioUpdate() {
  dispatch({t: "ContinuePlayback", cb: continuePlayback});
}
