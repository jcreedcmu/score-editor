import { h as hh, render, Component } from 'preact';
import { set_scroll } from './main';

class ScrollBars extends Component < any, any > {
  render({dims: {x, y, w, h}}) {
	 const style = {left: x, top: y, width: w, height: h};
	 const inner_style = {height: 3 * h};
	 const cb = (e) => {
		set_scroll((e.target as HTMLElement).scrollTop);
	 };
	 const c =
	 <div id="v_scroll" class="scroll_container"
			style={style}
			onScroll={cb}>
		<div class="scroll_content" style={inner_style}>
		</div>
	 </div>;
	 return c;
  }
}

export function component_render(x, y, w, h) {
  render(<ScrollBars dims={{x, y, w, h}}/>, document.body);
}
