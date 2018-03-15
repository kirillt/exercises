package widget;

import  flash.display.DisplayObjectContainer;

interface Widget {
	function place(
		x     : Float, y      : Float,
		width : Float, height : Float,
		stage : DisplayObjectContainer
	) : Void;
}
