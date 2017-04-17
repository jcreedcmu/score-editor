import { h as hh, render, Component } from 'preact';
import { Surface } from './surface';
import { dispatch } from './main';
import { Note, AppState } from './types';

const SCALE = 2; // units: pixels per fat pixel
const PIANO_H = 73;
const PIANO_W = 43;
const PIANO_OCTAVE_VSPACE = (PIANO_H - 1) * SCALE;
const PIANO_WIDTH = (PIANO_W) * SCALE;
const GUTTER_W = 8;
const GUTTER_WIDTH = GUTTER_W * SCALE;
const SCORE_W = 250;
const SCORE_WIDTH = 250 * SCALE;
const FAT_PIXELS_PER_TICK = 6;
const PIXELS_PER_TICK = FAT_PIXELS_PER_TICK * SCALE;
const PITCH_HEIGHT = 6;
const BASIC_PITCH_AT_Y0 = -1 + 12 * 6;

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

// I find this just helps guide my eye
function draw_gutter(d, x, y, w) {
  d.fillStyle = "black";
  d.save();
  d.translate(x, y);
  box(d, 0, 0, w, PIANO_H, 1, "#262626", "black")

  for (let n = 0; n < 12; n++) {
	 if (keytype[n]) {
		box(d, w - 7, PITCH_HEIGHT * n, 5, 7, 1, "#141414", "black");
	 }
  }

  d.restore();
}

type Rect = [number, number, number, number]; // x y w h, in canvas pixels
type Camera = {x: number, y: number};

function rect_of_note(n: Note, c: Camera): Rect {
  return [c.x + n.time[0] * PIXELS_PER_TICK,
			 c.y - n.pitch * PITCH_HEIGHT * SCALE,
			 (n.time[1] - n.time[0]) * PIXELS_PER_TICK + SCALE,
			 SCALE * (PITCH_HEIGHT + 1)];
}

function draw_notes(d, notes: Note[], camera: Camera) {
  notes.forEach(note => {
	 const r = rect_of_note(note, camera);
	 d.fillStyle = "black";
	 d.fillRect.apply(d, r);
	 d.fillStyle = colors[note.pitch % 12];
	 d.fillRect.apply(d, inset(r));
  });
}

function get_camera(scroll: number): Camera {
  return {x: PIANO_WIDTH + GUTTER_WIDTH,
			 y: (BASIC_PITCH_AT_Y0 - scroll) * PITCH_HEIGHT * SCALE};
}

function inset(rect: Rect): Rect {
  return [rect[0] + SCALE, rect[1] + SCALE, rect[2] - 2 * SCALE, rect[3] - 2 * SCALE];
}

function draw_piano_octave(d, x, y) {
  d.save();
  d.translate(x, y);
  box(d, 0, 0, PIANO_W, PIANO_H, 1, "#f8f8d8", "black");
  d.fillStyle = "black";
  [10, 21, 32, 42, 52, 62].forEach(wks =>
											  d.fillRect(0, wks * SCALE, PIANO_W * SCALE, 1 * SCALE)
											 );
  [1, 3, 5, 8, 10].forEach(bk =>
									box(d, 0, PITCH_HEIGHT * bk, 25, PITCH_HEIGHT + 1, 1, "#2e2234", "black")
								  );

  d.restore();
}

function draw_staff_octave(d, x, y, w) {
  d.fillStyle = "black";
  d.save();
  d.translate(x, y);
  d.fillRect(0, 0, w * SCALE, PIANO_H * SCALE);
  for (let n = 0; n < 12; n++) {
	 d.fillStyle = keytype[n] ? "#141414" : "#262626";
	 d.fillRect(SCALE, (PITCH_HEIGHT * n + 1) * SCALE, (w-2) * SCALE, (PITCH_HEIGHT - 1) * SCALE);
  }
  d.restore();
}

type ScoreEditorMainProps = ScoreEditorProps & { scroll: number };
class ScoreEditorMain extends Surface < ScoreEditorMainProps > {
  extraAttrs(props) {
	 return {style: {position: "absolute"}};
  }

  shouldComponentUpdate(p) {
	 return false; // xxx should reflect changes in notes
  }

  paint(props: ScoreEditorMainProps) {
	 const {scroll, score: {notes}} = props;

	 const d = this.ctx;
	 if (this.w != props.w || this.h != props.h)
		this.setDims(props.w, props.h);

	 d.clearRect(0, 0, this.w, this.h);
	 for (let oc = 0; oc < 3; oc++) {
		draw_piano_octave(d, 0, oc * PIANO_OCTAVE_VSPACE);
		draw_gutter(d, PIANO_WIDTH + SCALE, oc * PIANO_OCTAVE_VSPACE, 10);
		draw_staff_octave(d, PIANO_WIDTH + GUTTER_WIDTH, 0 + oc * PIANO_OCTAVE_VSPACE, 250);
	 }
	 draw_notes(d, notes, get_camera(scroll));
  }
}

// XXX rename 'time' to 'ticks'
type mpoint = { pitch: number, time: number } // point in "musical coordinates"
type cpoint = { x: number, y: number } // point measured in pixels from the topleft of the canvas

function mpoint_of_cpoint(cp: cpoint): mpoint {
  return {
	 pitch: BASIC_PITCH_AT_Y0 - Math.floor(cp.y / (SCALE * PITCH_HEIGHT)),
	 time: (cp.x - (PIANO_WIDTH + GUTTER_WIDTH + SCALE)) / PIXELS_PER_TICK,
  };
}

function note_of_mpoint({pitch, time}: mpoint): Note {
  return {pitch, time: [time, time + 3]};
}

class ScoreEditorOverlay extends Surface < ScoreEditorProps > {
  extraAttrs(props) {
	 return {style: {position: "absolute"}};
  }

  onmousemove(p, e) {
	 const pr: ScoreEditorProps = this.props;
	 const notes = pr.score.notes;
	 notes.forEach(note => {

	 });
	 dispatch({t: "PreviewNote", note: note_of_mpoint(mpoint_of_cpoint(p)) });

  }
  onmousedown(p, e) {

  }
  onmouseleave(e) {
	 dispatch({t: "PreviewNote", note: null});
  }

  shouldComponentUpdate(p) {
	 // XXX mmmmaybe should also check if score changes. Technically the overlay seems like it ought
	 // to change if, for example, a note shows up directly under the cursor. But that would seem
	 // to require *storing* the mouse position somewhere, which I'm not sure I like.

	 const now = this.props;
	 return (now.offsetTicks != p.offsetTicks) ||
	 (now.previewNote != p.previewNote && JSON.stringify(now.previewNote) != JSON.stringify(p.previewNote));
  }

  paint(props: ScoreEditorProps) {
	 if (this.w != props.w || this.h != props.h)
		this.setDims(props.w, props.h);
	 const d = this.ctx;
	 d.clearRect(0, 0, this.w, this.h);
	 if (props.previewNote != null) {
		const rect = rect_of_note(props.previewNote, get_camera(0 /* xxx scroll*/));
		d.fillStyle = "white";
		d.fillRect.apply(d, rect);
		d.clearRect.apply(d, inset(rect));
	 }
	 if (props.offsetTicks != null) {
		d.fillStyle = "white";
		d.fillRect(PIANO_WIDTH + GUTTER_WIDTH + SCALE * FAT_PIXELS_PER_TICK * props.offsetTicks, 0,
					  2, PIANO_OCTAVE_VSPACE * 3);
	 }
  }
}

class ScoreEditor extends Component < any, any > {
  render(props, state) {
	 const {w, h} = props;
	 const s = getScrollbarDims();
	 const style = {width: w, height: h,
						 position: "relative", display: "inline-block"};
	 const vscroller =
	 <div style={{height: h, left: w, width: s.width, "overflow-x": "hidden",
			"overflow-y": "scroll", position: "absolute"}}>
		<div style={{height: 2*h}}></div>
	 </div>;
	 const hscroller =
	 <div style={{height: s.height, top: h, left: PIANO_WIDTH + GUTTER_WIDTH,
			width: w - PIANO_WIDTH - GUTTER_WIDTH, "overflow-y": "hidden",
			"overflow-x": "scroll", position: "absolute"}}>
		<div style={{width: 2*w}}>&nbsp;</div>
	 </div>;

	 const c =
	 <div style={style}>
		<ScoreEditorMain {...props} scroll={0}/>
		<ScoreEditorOverlay {...props}/>
		{vscroller}
		{hscroller}
	 </div>;
	 return c;
  }
}

type ScoreEditorProps = AppState & {w: number, h: number};
export function component_render(scoreprops: AppState) {
  const props = {
	  ...scoreprops,
	 w: PIANO_WIDTH + GUTTER_WIDTH + SCORE_WIDTH,
	 h: PIANO_OCTAVE_VSPACE * 3 + SCALE
  };
  const cont = document.getElementById('canvas_container');
  render(<ScoreEditor {...props}/>, cont, cont.lastElementChild);
}

declare global {
   interface Window {
 	  scrollbarDims: {width: number, height: number};
   }
}

// simplified version of
// http://stackoverflow.com/questions/986937/how-can-i-get-the-browsers-scrollbar-sizes
function getScrollbarDims() {
  if (!window.scrollbarDims) {
	 const div = document.createElement('div');
	 div.innerHTML = '<div style="width:1px;height:1px;overflow:scroll;"></div>';
	 const c = div.firstChild as HTMLElement;
	 document.body.appendChild(c);
	 const width = c.offsetWidth - c.clientWidth;
	 const height = c.offsetHeight - c.clientHeight;
	 document.body.removeChild(c);
	 window.scrollbarDims = {width,height};
  }
  return window.scrollbarDims;
}
