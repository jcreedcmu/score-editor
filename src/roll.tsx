import { h as hh, Component } from 'preact';
import { y0pitch_of_scrollOctave, mpoint, RollMouseState } from './roll-util';
import { Surface } from './surface';
import { dispatch } from './main';
import { Note, cpoint, Pattern } from './types';
import { DerivedState } from './state';
import {
  SCALE,
  PIANO_H,
  PIANO_W,
  PIANO_OCTAVE_VSPACE,
  PIANO_WIDTH,
  GUTTER_WIDTH,
  FAT_PIXELS_PER_TICK,
  PIXELS_PER_TICK,
  PITCH_HEIGHT,
  BLACK_NOTE_WIDTH
} from './roll-util';

export type Style = "piano" | "drums";

export type RollEditorProps = {
  offsetTicks: number | null,
  debugOffsetTicks: number | null,
  useOffsetTicks: number,
  mouseState: RollMouseState,
  gridSize: number,
  noteSize: number,
  scrollOctave: number,
  style: Style,
  pattern: Pattern,
} & DerivedState & { w: number, h: number };

type RollEditorMainProps = RollEditorProps & { scroll: number };

type Rect = [number, number, number, number]; // x y w h, in canvas pixels
type Camera = { x: number, y: number };

function box(d, x, y, w, h, border, c, bc) {
  d.fillStyle = bc;
  d.fillRect(x * SCALE, y * SCALE, w * SCALE, h * SCALE);
  d.fillStyle = c;
  d.fillRect((x + border) * SCALE, (y + border) * SCALE, (w - 2 * border) * SCALE, (h - 2 * border) * SCALE);
}

const note_name = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "Ab", "A", "Bb", "B"];

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

const LIGHTER_DARK_GRAY = "#262626";
const DARKER_DARK_GRAY = "#141414";

const keytype = [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0];

// I find this just helps guide my eye
function draw_gutter(d, x, y, w, style: Style) {
  d.fillStyle = "black";
  d.save();
  d.translate(x, y);
  box(d, 0, 0, w, PIANO_H, 1, LIGHTER_DARK_GRAY, "black")

  if (style == "piano") {
    for (let n = 0; n < 12; n++) {
      if (keytype[n]) {
        box(d, w - 7, PITCH_HEIGHT * n, 5, PITCH_HEIGHT + 1, 1, DARKER_DARK_GRAY, "black");
      }
    }
  }

  d.restore();
}

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

function get_camera(scrollOctave: number): Camera {
  return {
    x: PIANO_WIDTH + GUTTER_WIDTH,
    y: y0pitch_of_scrollOctave(scrollOctave) * PITCH_HEIGHT * SCALE
  };
}

function inset(rect: Rect): Rect {
  return [rect[0] + SCALE, rect[1] + SCALE, rect[2] - 2 * SCALE, rect[3] - 2 * SCALE];
}

function draw_piano_octave(d, x, y) {
  d.save();
  d.translate(x, y);
  box(d, 0, 0, PIANO_W, PIANO_H, 1, "#f8f8d8", "black");
  d.fillStyle = "black";
  [14, 28, 42, 56, 69, 83].forEach(wks =>
    d.fillRect(0, wks * SCALE, PIANO_W * SCALE, 1 * SCALE)
  );
  [1, 3, 5, 8, 10].forEach(bk =>
    box(d, 0, PITCH_HEIGHT * bk, BLACK_NOTE_WIDTH, PITCH_HEIGHT + 1, 1, "#2e2234", "black")
  );

  d.restore();
}

function draw_staff_octave(d, x, y, w, style: Style, gridSize: number) {
  const effectiveGridSize = 4; // enh... 'visibleGridSize'? ignores gridSize argument.
  d.fillStyle = "black";
  d.save();
  d.translate(x, y);
  d.fillRect(0, 0, w * SCALE, PIANO_H * SCALE);
  for (let n = 0; n < 12; n++) {
    d.fillStyle = keytype[n] || style == "drums" ? DARKER_DARK_GRAY : LIGHTER_DARK_GRAY;
    d.fillRect(SCALE, (PITCH_HEIGHT * n + 1) * SCALE, (w - 2) * SCALE, (PITCH_HEIGHT - 1) * SCALE);
  }
  d.fillStyle = "black";
  for (let n = 0; n * PIXELS_PER_TICK * effectiveGridSize < SCALE * w; n++) {
    d.fillRect(n * PIXELS_PER_TICK * effectiveGridSize, 0, SCALE, PIANO_H * SCALE);
  }
  d.restore();
}

class RollEditorMain extends Surface<RollEditorMainProps> {
  extraAttrs(props) {
    return { style: { position: "absolute" } };
  }

  shouldComponentUpdate(p) {
    return JSON.stringify(p.pattern) != JSON.stringify(this.props.pattern) ||
      p.scrollOctave != this.props.scrollOctave ||
      p.noteSize != this.props.noteSize ||
      p.gridSize != this.props.gridSize;
  }

  paint(props: RollEditorMainProps) {
    const { scrollOctave, pattern } = props;
    const { notes, length } = pattern;

    const d = this.ctx;
    if (this.w != props.w || this.h != props.h)
      this.setDims(props.w, props.h);

    d.fillStyle = LIGHTER_DARK_GRAY;
    d.fillRect(0, 0, this.w, this.h);
    for (let oc = 0; oc < 3; oc++) {
      if (props.style == "piano") {
        draw_piano_octave(d, 0, oc * PIANO_OCTAVE_VSPACE);
      }
      draw_gutter(d, PIANO_WIDTH + SCALE, oc * PIANO_OCTAVE_VSPACE, 10, props.style);
      draw_staff_octave(d, PIANO_WIDTH + GUTTER_WIDTH, 0 + oc * PIANO_OCTAVE_VSPACE, length * FAT_PIXELS_PER_TICK + 1, props.style, props.gridSize);
    }
    draw_notes(d, notes, get_camera(scrollOctave));
  }
}

class RollEditorOverlay extends Surface<RollEditorProps> {
  extraAttrs(props) {
    return { style: { position: "absolute" } };
  }

  onmousemove(p, e) {
    dispatch({ t: "Mousemove", p });
  }

  onmousedown(p, e) {
    dispatch({ t: "Mousedown", p });
  }

  onmouseleave(e) {
    dispatch({ t: "Mouseleave" });
  }

  shouldComponentUpdate(p) {
    const now = this.props;
    return (now.offsetTicks != p.offsetTicks) ||
      (now.previewNote != p.previewNote && JSON.stringify(now.previewNote) != JSON.stringify(p.previewNote)) ||
      (now.gridSize != p.gridSize) ||
      (now.noteSize != p.noteSize);
  }

  paint(props: RollEditorProps) {
    if (this.w != props.w || this.h != props.h)
      this.setDims(props.w, props.h);
    const d = this.ctx;
    d.clearRect(0, 0, this.w, this.h);
    if (props.previewNote != null) {
      const rect = rect_of_note(props.previewNote, get_camera(props.scrollOctave));
      d.fillStyle = "white";
      d.textAlign = "right";
      d.textBaseline = "middle";
      d.font = "bold 10px sans-serif ";

      const pitch = props.previewNote.pitch;
      const annot = (props.style == "drums" ? pitch : note_name[pitch % 12]) as string;
      d.fillText(annot, rect[0] - 1, rect[1] + 1 + rect[3] / 2);
      d.fillRect.apply(d, rect);
      d.clearRect.apply(d, inset(rect));
    }

    // draw playback cursor
    if (props.offsetTicks != null) {
      const relToUse = props.offsetTicks - props.useOffsetTicks;
      if (relToUse >= 0 && relToUse < props.pattern.length) {
        d.fillStyle = "white";
        d.fillRect(PIANO_WIDTH + GUTTER_WIDTH + SCALE * FAT_PIXELS_PER_TICK * (props.offsetTicks - props.useOffsetTicks), 0,
          2, PIANO_OCTAVE_VSPACE * 3);
      }
    }
  }
}

class VScrollBar extends Component<any, any> {
  _elt: Element;

  render(props) {
    const s = getScrollbarDims();
    const { height, content_height, x, y, onScroll } = props;
    const c =
      <div style={{
        height, left: x, top: y, width: s.width, "overflow-x": "hidden",
        "overflow-y": "scroll", position: "absolute"
      }}
        onScroll={() => onScroll(this._elt.scrollTop)}
        ref={x => this._elt = x}>
        <div style={{ height: content_height }}></div>
      </div>;
    return c;
  }

  componentDidMount() {
    this._elt.scrollTop = this.props.scrollTop;
  }

  componentDidUpdate() {
    this._elt.scrollTop = this.props.scrollTop;
  }
}

export class RollEditor extends Component<any, any> {
  render(props: RollEditorProps, state) {
    const { w, h } = props;
    const s = getScrollbarDims();
    const style = {
      width: w, height: h,
      position: "relative", display: "inline-block"
    };
    const onVscroll = top => dispatch({ t: "Vscroll", top: Math.round(3 * top / h) });
    const vscroller = <VScrollBar height={h}
      scrollTop={props.scrollOctave * h / 3}
      onScroll={onVscroll}
      content_height={(7 / 3) * h}
      x={w} y={0} />;
    const hscroller =
      <div style={{
        height: s.height, top: h, left: PIANO_WIDTH + GUTTER_WIDTH,
        width: w - PIANO_WIDTH - GUTTER_WIDTH, "overflow-y": "hidden",
        "overflow-x": "scroll", position: "absolute"
      }}>
        <div style={{ width: 2 * w }}>&nbsp;</div>
      </div>;

    const cursorState = props.mouseState.t == "resizeNote" ? "resize" : null;

    const REM: any = RollEditorMain;
    const REO: any = RollEditorOverlay;

    const c =
      <div>
        <img className="button" src="img/back.png" onClick={() => dispatch({ t: "EditSong" })}></img><br />
        <div style={style} className={cursorState} >
          <REM {...props} scroll={0} />
          <REO {...props} />
          {vscroller}
          {hscroller}
        </div>
      </div>;
    return c;
  }
}

declare global {
  interface Window {
    scrollbarDims: { width: number, height: number };
  }
}

// simplified version of
// http://stackoverflow.com/questions/986937/how-can-i-get-the-browsers-scrollbar-sizes
function getScrollbarDims() {
  if (!window.scrollbarDims) {
    const div = document.createElement('div');
    div.innerHTML = '<div style="width:100px;height:100px;overflow:scroll;"></div>';
    const c = div.firstChild as HTMLElement;
    document.body.appendChild(c);
    const width = c.offsetWidth - c.clientWidth;
    const height = c.offsetHeight - c.clientHeight;
    document.body.removeChild(c);
    window.scrollbarDims = { width, height };
  }
  return window.scrollbarDims;
}
