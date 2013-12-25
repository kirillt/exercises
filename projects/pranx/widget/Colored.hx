package widget;

import  flash.display.Sprite;
import  flash.display.DisplayObjectContainer;

class Colored implements Widget {

	var color  : Int;
	var sprite : Sprite;

	public function new(color : Int) {
		this.sprite = new Sprite();
		this.color = color;
	}

	public function place(
		x     : Float, y      : Float,
		width : Float, height : Float,
		scene : DisplayObjectContainer) {

		scene.addChild(sprite);
		sprite.graphics.beginFill(color);
		sprite.graphics.drawRect(x,y,width,height);
		sprite.graphics.endFill();
	}
}
