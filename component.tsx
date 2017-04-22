import { h as hh, render, Component } from 'preact';
import { RollEditor, rollDims } from './roll';
import { Minibuffer } from './minibuf';
import { dispatch } from './main';
import { AppState } from './types';
import * as CSSTransitionGroup from 'preact-css-transition-group';

export function component_render(scoreprops: AppState) {
  const props = {
	  ...scoreprops,
	  ...rollDims
  };
  const cont = document.getElementById('canvas_container');
  const playClick = () => dispatch({t: "Play", score: scoreprops.score});

  const cc = <div>
		<button onClick={playClick}>Play</button><br/>
		<RollEditor {...props}/>
		<div>
		  <div className="minibuffer">
			 <CSSTransitionGroup transitionName="minibuf">
				{props.minibufferVisible ? <Minibuffer key="minibuf"
																	value={props.minibuf}
																	send={cmd => dispatch({t:"ExecMinibuf", cmd})} /> : ''}
			 </CSSTransitionGroup>
		  </div>
		</div>
  </div>;
  render(cc, cont, cont.lastElementChild);
}
