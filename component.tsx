import { h as hh, render, Component } from 'preact';
import { Surface } from './surface';
import { dispatch } from './main';
// class ScrollBars extends Component < any, any > {
//   render({dims: {x, y, w, h}}) {
// 	 const style = {left: x, top: y, width: w, height: h};
// 	 const inner_style = {height: 3 * h};
// 	 const cb = (e) => {
// 		set_scroll((e.target as HTMLElement).scrollTop);
// 	 };
// 	 const c =
// 	 <div id="v_scroll" class="scroll_container"
// 			style={style}
// 			onScroll={cb}>
// 		<div class="scroll_content" style={inner_style}>
// 		</div>
// 	 </div>;
// 	 return c;
//   }
// }

const SCALE = 2;
const PIANO_H = 73;
const PIANO_W = 43;
const PIANO_OCTAVE_VSPACE = (PIANO_H - 1) * SCALE;
const PIANO_WIDTH = (PIANO_W) * SCALE;
const GUTTER_W = 8;
const GUTTER_WIDTH = GUTTER_W * SCALE;
const SCORE_W = 250;
const SCORE_WIDTH = 250 * SCALE;
const FAT_PIXELS_PER_TICK = 6;
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
function gutter(d, x, y, w) {
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

function render_notes(d, notes, x, y, pitch_at_y0, ticks_at_x0, fat_pixels_per_tick) {
  d.save();
  d.translate(x, y);
  notes.forEach(note => {
	 const nx = (note.time[0] - ticks_at_x0) * fat_pixels_per_tick;
	 const nw = (note.time[1] - note.time[0]) * fat_pixels_per_tick + 1;
	 const ny = (pitch_at_y0 - note.pitch) * PITCH_HEIGHT;
	 const nh = PITCH_HEIGHT + 1;
	 box(d, nx, ny, nw, nh, 1, colors[note.pitch % 12], "black")
  });
  d.restore();
}

function octave(d, x, y) {
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

function staff_octave(d, x, y, w) {
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

class ScoreEditorMain extends Surface < any > {
  extraAttrs(props) {
	 return {style: {position: "absolute"}};
  }

  shouldComponentUpdate(p) {
	 return false; // xxx should reflect changes in notes
  }

  paint(props) {
	 const {scroll, notes} = props;
	 const d = this.ctx;
	 if (this.w != props.w || this.h != props.h)
		this.setDims(props.w, props.h);

	 d.clearRect(0, 0, this.w, this.h);
	 for (let oc = 0; oc < 3; oc++) {
		octave(d, 0, oc * PIANO_OCTAVE_VSPACE);
		gutter(d, PIANO_WIDTH + SCALE, oc * PIANO_OCTAVE_VSPACE, 10);
		staff_octave(d,  + PIANO_WIDTH + GUTTER_WIDTH, 0 + oc * PIANO_OCTAVE_VSPACE, 250);
	 }

	 render_notes(d, notes, PIANO_WIDTH + GUTTER_WIDTH, 0,
					  BASIC_PITCH_AT_Y0 - scroll, 0, FAT_PIXELS_PER_TICK);

  }
}

class ScoreEditorOverlay extends Surface < any > {
  extraAttrs(props) {
	 return {style: {position: "absolute"}};
  }

  onmousemove(p, e) {
	 dispatch({t: "PreviewNote", note: { pitch: BASIC_PITCH_AT_Y0 - Math.floor(p.y / (SCALE * PITCH_HEIGHT)),
													 time: [0, 3] } });
  }
  onmousedown(p, e) {

  }
  onmouseleave(e) {
	 dispatch({t: "PreviewNote", note: null});
  }

  shouldComponentUpdate(p) {
	 const now = this.props;
	 return (now.offsetTicks != p.offsetTicks) ||
	 (now.previewNote != p.previewNote && JSON.stringify(now.previewNote) != JSON.stringify(p.previewNote));
  }

  paint(props) {
	 if (this.w != props.w || this.h != props.h)
		this.setDims(props.w, props.h);
	 const d = this.ctx;
	 d.clearRect(0, 0, this.w, this.h);
	 if (props.previewNote != null) {
		d.fillStyle = "white";
		const rect = [PIANO_WIDTH + GUTTER_WIDTH + SCALE * FAT_PIXELS_PER_TICK * props.previewNote.time[0] + SCALE,
					  (BASIC_PITCH_AT_Y0 - props.previewNote.pitch) * PITCH_HEIGHT * SCALE,
					  100, (PITCH_HEIGHT + 1) * SCALE];
		d.fillRect(rect[0], rect[1], rect[2], rect[3]);
		d.clearRect(rect[0] + SCALE, rect[1] + SCALE, rect[2] - 2 * SCALE, rect[3] - 2 * SCALE);
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

export function component_render(scoreprops) {
  //  render(<ScrollBars dims={{x, y, w, h}}/>, document.body);
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
