import { h as hh, Component } from 'preact';
import { dispatch } from './main';

export class SongEditor extends Component< any, any > {
  render(props) {
	 const pixels_per_tick = 3;
	 const bits = props.score.song.map(pu => {
		const style = { left: pu.start * pixels_per_tick, width: pu.duration * pixels_per_tick };
		const odc = (e) => {
		  e.preventDefault();
		  dispatch({t: "EditPat", patName: pu.patName});
		}
		// jsx types don't like onDblClick??
		return hh("div", {className: "use",
								style,
								onMouseDown: (e) => e.preventDefault(),
								onDblClick: odc}, <div>{pu.patName}</div>);
	 });
	 let cursor = null;
	 if (props.offsetTicks != null) {
		const cstyle = {left: props.offsetTicks * pixels_per_tick };
		cursor = <div className="cursor" style={cstyle}></div>;
	 }
	 return <div className="songEditor">{bits}{cursor}</div>;
  }
}
