package layout;

import  log.Logger;

import  widget.Widget;

import  flash.display.DisplayObjectContainer;

typedef Item = {
	x      : Float, y      : Float,
	width  : Float, height : Float,
	widget : Widget
}

class Layout implements Widget {
	var logger : Logger;

	var items  : List<Item>;
	var queue  : List<Item>;
	var scene  : DisplayObjectContainer;

	public var x      : Float;
	public var y      : Float;
	public var width  : Float;
	public var height : Float;

	private function new(scene : DisplayObjectContainer,
		logger : Logger) {

		this.logger = logger;

		this.items  = new List<Item>();
		this.queue  = new List<Item>();
		this.scene  = scene;
	}

	private function display(queue : List<Item>) {
		throw "Not implemented - abstract class.";
	}

	public function displayNew() {
		display(queue);
	}

	public function redraw() {
		logger.log('Redrawing layout.');
		queue = items;
		displayNew();
	}

	public function place(
		x     : Float, y      : Float,
		width : Float, height : Float,
		scene : DisplayObjectContainer) {

		if (this.scene != scene) {
			throw "Trying to place layout not on it's stage.";
		}

		this.x      = x;
		this.y      = y;
		this.width  = width;
		this.height = height;

		redraw();
	}

	public function addWidget(
		x      : Float, y      : Float,
		width  : Float, height : Float,
		widget : Widget) {

		addItem({
			x:x,         y:y,
			width:width, height:height,
			widget:widget}
		);
	}

	public function addItem(item : Item) {
		if (item.x     < 0 && item.y     < 0 &&
			item.width < 0 && item.height < 0) {
			throw 'Illegal arguments: negative numbers.';
		} else {
			items.add(item);
			queue.add(item);
			logger.log('Item added: ');
			logItem(item);
		}
	}

	public function removeWidget(
		widget : Widget) {

		logger.log('Removing widget:');
		logger.indent++;
		for (item in items) {
			if (item.widget == widget) {
				removeItem(item);
				logItem(item);
			}
		}
		logger.indent--;
	}

	public function removeItem(item : Item) {
		items.remove(item);
		queue.remove(item);
		logger.log('Item removed:\t');
		logItem(item);
	}

	public function getItems() {
		return items.iterator();
	}

	public function logItem(item : Item) {
		logger.logAppend(
			item.x + ' [' + item.width + '], ' +
			item.y + ' [' + item.height + ']');
	}
}
