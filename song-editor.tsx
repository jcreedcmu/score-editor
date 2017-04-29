import { h as hh, Component } from 'preact';
import { dispatch } from './main';

export const PIXELS_PER_TICK = 3;

export class SongEditor extends Component< any, any > {
  render(props) {

	 function pos(e: MouseEvent) {
		const br = (e.target as HTMLElement).getBoundingClientRect();
		return {pitch:0, time:0, x: e.clientX - br.left, y: e.clientY - br.top};
	 }
 	 const omd = (e) => { e.preventDefault(); dispatch({t: "Mousedown", mpoint: pos(e)}); }
 	 const omm = (e) => { e.preventDefault(); dispatch({t: "Mousemove", mpoint: pos(e)}); }

	 const bits = props.score.song.map(pu => {
		const style = { left: pu.start * PIXELS_PER_TICK, width: pu.duration * PIXELS_PER_TICK };
		return <div className="use" style={style}><div>{pu.patName}</div></div>;
	 });
	 let cursor = null;
	 if (props.offsetTicks != null) {
		const cstyle = {left: props.offsetTicks * PIXELS_PER_TICK };
		cursor = <div className="cursor" style={cstyle}></div>;
	 }
	 return <div className="songEditor"
					 onMouseDown={omd}
					 onMouseMove={omm}>{bits}{cursor}</div>;
  }
}
