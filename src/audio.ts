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

// Leave behind some breadcrumbs about contiguous chunks we've
// rendered, so we can properly communicate upstream where in the song
// we're currently playing.
type NowTicksChunk = {
  startSecs: number,
  startTicks: number,
  durationSecs: number,
  secsPerTick: number
}

type AudioState = {
  nextUpdateTimeout? : number,
  renderedUntil?: number, // seconds
  renderedUntilSong? : number, // ticks
  liveNotes: NoteState[],
  nowTicks: NowTicksChunk[],
}

const state : AudioState = {
  liveNotes: [],
  nowTicks: [],
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

// Same as renderChunkInto below, except
// (a) only fill the part of dat starting at datStart and proceeding for datDuration frames
// (b) we're guaranteed the interval [startTicks, startTicks + datDuration * frames_per_tick]
//     is logically contiguous; i.e. doesn't wrap across a loop point.
function renderContiguousChunkInto(dat: Float32Array, datStart: number, datDuration: number,
											  startTicks: number, score: Score, liveNotes: NoteState[]): NoteState[] {

  const newLiveNotes = [];
  for (const note of collectNotes(score, startTicks, datDuration / (score.seconds_per_tick * RATE))) {
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
		  dat[datStart + i] += env * 0.15 * ((noteState.phase - Math.floor(noteState.phase)) < 0.5 ? 0.2 : -0.2);
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
		  dat[datStart + i] += env * volumeAdjust * noteState.buf;
		}
		break;
	 }
  }
  return newLiveNotes;
}

type RenderChunkResult = {
  liveNotes: NoteState[],
  renderedUntilSong: number,
  nowTicks: NowTicksChunk[],
}

// Starting at song-time `startTicks`, given score `score`, assuming `liveNotes` notes exist from
// the previous chunk render, fill the audio buffer `dat` with samples, returning
// {liveNotes: the set of notes that are still active,
//  nowTicks: a list of mappings from real time to song time, relative to the beginning of this rendering,
//            i.e. startSecs of the first item will always be 0 and we trust the caller to bump it up to
//            the current time}
function renderChunkInto(dat: Float32Array, startTicks: number, score: Score, liveNotesIn: NoteState[]): RenderChunkResult {
  if (score.loop_end <= score.loop_start) { throw "invariant violation, loop markers can't be badly ordered" }

  const ticks_to_render = dat.length / (score.seconds_per_tick * RATE);
  if (startTicks < score.loop_start) startTicks = score.loop_start;
  if (startTicks + ticks_to_render <= score.loop_end) {
	 const liveNotes = renderContiguousChunkInto(dat, 0, dat.length, startTicks, score, liveNotesIn);
	 const nowTicks: NowTicksChunk[] = [
		{
		  startSecs: 0,
		  startTicks,
		  durationSecs: dat.length / RATE,
		  secsPerTick: score.seconds_per_tick
		}
	 ];
	 const renderedUntilSong = startTicks + ticks_to_render;
	 return {liveNotes, nowTicks, renderedUntilSong};
  }
  else {
	 const fragLength = Math.round((score.loop_end - startTicks) * (score.seconds_per_tick * RATE)); // frames
	 const liveNotes0 = renderContiguousChunkInto(dat, 0, fragLength, startTicks, score, liveNotesIn);
	 const liveNotes = renderContiguousChunkInto(dat, fragLength, dat.length - fragLength, score.loop_start, score, liveNotes0);
	 const renderedUntilSong = score.loop_start + ticks_to_render - fragLength / (score.seconds_per_tick * RATE);
	 const nowTicks: NowTicksChunk[] = [
		{
		  startSecs: 0,
		  startTicks,
		  durationSecs: fragLength / RATE,
		  secsPerTick: score.seconds_per_tick
		},
		{
		  startSecs: fragLength / RATE,
		  startTicks: score.loop_start,
		  durationSecs: (dat.length - fragLength) / RATE,
		  secsPerTick: score.seconds_per_tick
		}
	 ];
	 return {liveNotes, nowTicks, renderedUntilSong};
  }
}

// t is in seconds, return value is in ticks
function nowTicks(chunks: NowTicksChunk[], t: number): number {
  for (let i = 0; i < chunks.length; i++) {
	 const ch = chunks[i];
	 if (t >= ch.startSecs && t < ch.startSecs + ch.durationSecs) {
		return ch.startTicks + (t - ch.startSecs) / ch.secsPerTick;
	 }
  }
  throw `trying to determine song position of unrendered audio: ${t} not in ${JSON.stringify(chunks)}`;
}

function continuePlayback(score: Score): Progress {
  const now = ad.currentTime;

  // do we need to render?
  if ((state.renderedUntil - now) < COAST_MARGIN) {
	 const render_chunk_size_seconds = RENDER_CHUNK_SIZE / RATE;
	 const buf = ad.createBuffer(1 /* channel */, RENDER_CHUNK_SIZE, RATE);
	 const dat: Float32Array = buf.getChannelData(0);
	 const {liveNotes, renderedUntilSong, nowTicks} = renderChunkInto(dat, state.renderedUntilSong, score, state.liveNotes);
	 state.liveNotes = liveNotes;
	 state.renderedUntilSong = renderedUntilSong;

	 // As noted above, renderChunkInto gives us startSecs relative to
	 // the beginning of the renderedChunk. Adjust it to relative to
	 // audio context initialization time.
	 const nowTicksAbsolute = nowTicks.map(nt => ({...nt, startSecs: nt.startSecs + now}));

	 state.nowTicks = state.nowTicks.filter(nt => nt.startSecs + nt.durationSecs >= now).concat(nowTicksAbsolute);

	 const src = ad.createBufferSource();
	 src.buffer = buf;
	 src.connect(ad.destination);

	 // I expect
	 //
	 //     state.renderedUntil * RATE
	 //
	 // to stay very close to an integer (because audio context's
	 // "currentTime" seems to stay essentially an integer multiple of
	 // 1/RATE) although since I'm incrementing by floating point
	 // quantities of seconds, I observe it drifting by something on
	 // the order of 1e-8 seconds per second. Maybe could keep track of
	 // renderedUntilFrames as an integer instead. (no chance it'll get
	 // anywhere close to Number.MAX_SAFE_INTEGER in practice, I think)
	 src.start(state.renderedUntil);
	 state.renderedUntil += render_chunk_size_seconds;
  }

  state.nextUpdateTimeout = setTimeout(audioUpdate, UPDATE_INTERVAL * 1000);
  return {v: nowTicks(state.nowTicks, now)};
}

export function play() {
  if (state.nextUpdateTimeout) {
	 clearTimeout(state.nextUpdateTimeout);
  }

  state.liveNotes = [];
  state.renderedUntilSong = 0;
  state.renderedUntil = ad.currentTime + WARMUP_TIME;
  state.nextUpdateTimeout = setTimeout(audioUpdate, 0);
}

export function stop() {
  if (state.nextUpdateTimeout != undefined) {
	 clearTimeout(state.nextUpdateTimeout);
	 state.nextUpdateTimeout = undefined;
  }
}
function audioUpdate() {
  dispatch({t: "ContinuePlayback", cb: continuePlayback});
}
