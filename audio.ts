import { Score } from './types';

export const ad = new AudioContext();
const RATE = ad.sampleRate; // most likely 44100, maybe 48000?

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

export function play(score, progress) {
  audio_render_notes(ad, score, progress);
}
