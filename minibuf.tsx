import { h as hh, Component } from 'preact';
import { dispatch } from './main';

export class Minibuffer extends Component < any, any > {
  _elt: HTMLInputElement;
  render(props, state) {
	 return <div className="mbcont">
		  <b>{"\u25B6"}</b>
		  <div className="input_container">
			 <input ref={e => this._elt = e as HTMLInputElement}
					  onKeyDown={(e) => { if (e.keyCode == 13) props.send();}}
					  onInput={x => dispatch({t: "SetMinibuf", v: this._elt.value})}
					  value={this.props.value}></input>
		  </div>
		</div>;
  }
  componentDidMount () {
	 this._elt.spellcheck = false; // setting this in the input props doesn't work, see https://github.com/developit/preact/issues/651
	 this._elt.focus();
  }
}
