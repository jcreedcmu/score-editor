import { h as hh, Component } from 'preact';
import { dispatch } from './main';

export const PIXELS_PER_TICK = 3;
export const LANE_HEIGHT = 50;

export class SongEditor extends Component< any, any > {
  _elt: HTMLElement;
  _bg: string;

  constructor() {
	 super();
	 const bg = document.createElement('canvas');
	 bg.height = LANE_HEIGHT;
	 bg.width = 1;
	 const d = bg.getContext('2d');
	 d.fillStyle = "#262626";
	 d.fillRect(0, 0, 1, LANE_HEIGHT - 1);
	 d.fillStyle = "black";
	 d.fillRect(0, LANE_HEIGHT - 1, 1, 1);
	 this._bg = "url(" + bg.toDataURL() + ")"
  }

  pos(e: MouseEvent) {
	 const br = this._elt.getBoundingClientRect();
	 return {x: e.clientX - br.left, y: e.clientY - br.top};
  }

  render(props) {
 	 const omd = (e) => { e.preventDefault(); dispatch({t: "Mousedown", p: this.pos(e)}); }
 	 const omm = (e) => { e.preventDefault(); dispatch({t: "Mousemove", p: this.pos(e)}); }

	 const bits = props.score.song.map(pu => {
		const style = {
		  top: pu.lane * LANE_HEIGHT - 1,
		  left: pu.start * PIXELS_PER_TICK - 1,
		  width: pu.duration * PIXELS_PER_TICK - 2 /* 2? 1? */,
		  height: LANE_HEIGHT - 1,
		};
		return <div className="use" style={style}><div>{pu.patName}</div></div>;
	 });
	 let cursor = null;
	 if (props.offsetTicks != null) {
		const cstyle = {left: props.offsetTicks * PIXELS_PER_TICK };
		cursor = <div className="cursor" style={cstyle}></div>;
	 }
	 const style = {
		"background-image": this._bg,
	 };
	 return <div className="songEditor"
					 ref={(e) => this._elt = e as HTMLElement}
					 style = {style}
					 onMouseDown={omd}
					 onMouseMove={omm}>{bits}{cursor}</div>;
  }
}
