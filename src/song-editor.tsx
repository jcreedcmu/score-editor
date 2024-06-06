import { h as hh, Component } from 'preact';
import { dispatch } from './main';
import { Immutable as Im, get, getIn, set, update, updateIn, fromJS, toJS } from './immutable';
import { AppState } from './state'
import { Pattern } from './types'
import { SongMode } from './song-util'

export const TICKS_PER_GRID = 16;
export const PIXELS_PER_GRID = 48;
export const LANE_HEIGHT = 50;
export const PIXELS_PER_TICK = PIXELS_PER_GRID / TICKS_PER_GRID;

// ambivariant function argument checking means this type annotation
// doesn't really buy me what I think it does. Oh well...
type SongAppState = AppState & { mode: SongMode }

export class SongEditor extends Component<{ state: Im<SongAppState> }, any> {
  _elt: HTMLElement;
  _bg: string;
  _useBgCache: { [P in string]: string } = {};

  constructor() {
    super();
    const bg = document.createElement('canvas');
    bg.height = LANE_HEIGHT;
    bg.width = PIXELS_PER_GRID;
    const d = bg.getContext('2d');
    d.fillStyle = "black";
    d.fillRect(0, 0, PIXELS_PER_GRID, LANE_HEIGHT);
    d.fillStyle = "#262626";
    d.fillRect(0, 0, PIXELS_PER_GRID - 1, LANE_HEIGHT - 1);
    this._bg = "url(" + bg.toDataURL() + ")"
  }

  pos(e: MouseEvent) {
    if (!this._elt) return { x: 0, y: 0 };
    const br = this._elt.getBoundingClientRect();
    return { x: e.clientX - br.left, y: e.clientY - br.top };
  }

  componentWillReceiveProps(nextProps: { state: Im<SongAppState> }) {
    if (get(nextProps.state, 'score') != get(this.props.state, 'score')) {
      for (let k of Object.keys(this._useBgCache)) {
        if (getIn(this.props.state, x => x.score.patterns[k].length) !=
          getIn(nextProps.state, x => x.score.patterns[k].length)) {
          delete this._useBgCache[k];
        }
      }
    }
  }

  getPatUseBackground(patName: string, pat: Im<Pattern>): string {
    if (this._useBgCache[patName] == undefined) {
      const bg = document.createElement('canvas');
      bg.height = LANE_HEIGHT;
      bg.width = PIXELS_PER_TICK * get(pat, 'length');
      const d = bg.getContext('2d');
      d.fillStyle = "#0c3535";
      d.fillRect(0, 0, bg.width, bg.height);
      d.fillStyle = "#075152";
      d.fillRect(0, 0, bg.width - 1, bg.height - 1);
      this._useBgCache[patName] = "url(" + bg.toDataURL() + ")";
    }
    return this._useBgCache[patName];
  }

  render({ state }: { state: Im<SongAppState> }) {
    const props: SongAppState = toJS(state);

    const omd = (e) => {
      e.preventDefault();
      let extra = undefined;
      if (e.target.getAttribute("class") == "marker") {
        extra = e.target.getAttribute("id");
      }
      dispatch({ t: "Mousedown", p: this.pos(e), extra });
    }
    const omm = (e) => { e.preventDefault(); dispatch({ t: "Mousemove", p: this.pos(e) }); }

    const bits = props.score.song.map(pu => {
      const pat = getIn(state, x => x.score.patterns[pu.patName]);
      const style = {
        top: pu.lane * LANE_HEIGHT - 1,
        left: pu.start * PIXELS_PER_TICK - 1,
        width: pu.duration * PIXELS_PER_TICK - 1,
        height: LANE_HEIGHT - 1,
        "background-image": this.getPatUseBackground(pu.patName, pat),
      };
      return <div className="use" style={style}><div>{pu.patName}</div></div>;
    });
    let cursor = null;
    if (props.offsetTicks != null) {
      const cstyle = { left: props.offsetTicks * PIXELS_PER_TICK };
      cursor = <div className="cursor" style={cstyle}></div>;
    }

    const loopStartStyle = { left: props.score.loop_start * PIXELS_PER_TICK - 3 };
    const loopEndStyle = { left: props.score.loop_end * PIXELS_PER_TICK - 3 };

    const loopStart = <div id="loop_start" className="marker" style={loopStartStyle}></div>;
    const loopEnd = <div id="loop_end" className="marker" style={loopEndStyle}></div>;

    const style = {
      "background-image": this._bg,
    };
    const classes = ["songEditor"];
    const mode: SongMode = props.mode;
    if (mode.mouseState.t == "moveLoopEndpoint")
      classes.push("resize");
    console.log('rendering');
    return <div className={classes.join(" ")}
      ref={(e) => {
        console.log('assigning _elt');
        this._elt = e as HTMLElement;
      }}
      style={style}
      onMouseDown={omd}
      onMouseMove={omm}>{bits}{cursor}{loopStart}{loopEnd}</div>;
  }
}
