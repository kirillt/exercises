package widget;

import  flash.display.DisplayObjectContainer;

class Empty implements Widget {
	public function new() {}

	public function place(
		x     : Float, y      : Float,
		width : Float, height : Float,
		scene : DisplayObjectContainer)
	{}
}
