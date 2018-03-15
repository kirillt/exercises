package layout;

import  Math;

import  log.Logger;

import  widget.Widget;

import  flash.display.DisplayObjectContainer;

typedef CachedSizeEnty = {
	width  : Float,
	height : Float,
	x      : Float,
	y      : Float
}

class GridLayout extends Layout {

	var matrix      : Matrix<Layout.Item>;

	var automatic   : List<Layout.Item>;
	var cachedSizes : List<CachedSizeEnty>;

	public function new(scene : DisplayObjectContainer,
		logger : Logger) {
		super(scene, logger);

		cachedSizes = new List<CachedSizeEnty>();
		automatic   = new List<Layout.Item>();
		matrix      = new Matrix<Layout.Item>(logger);
	}

	override
	function display(queue : List<Layout.Item>) {
		var cellWidth  = width  / matrix.sizeX;
		var cellHeight = height / matrix.sizeY;

		for (item in queue) {
			item.widget.place(
				this.x + cellWidth  * item.x,
				this.y + cellHeight * item.y,
				cellWidth  * item.width,
				cellHeight * item.height,
				scene);
			queue.remove(item);
		}
	}

	public function setAutomaticallyBySize(
		width   : Float, height  : Float,
		widget  : Widget) {

		setAutomaticallyBySizeWithMargin(
			width, height, 0, 0, widget);
	}

	public function setAutomaticallyBySizeWithMargin(
		width   : Float, height  : Float,
		marginX : Float, marginY : Float,
		widget  : Widget) {

		logger.log('Automatic insertion (by size):');
		logger.indent++;

		var x = 0;
		var y = 0;
		var point  = null;
		var pointF = getCachedSize(width, height);
		if (pointF != null) {
			x = toInt(pointF.x);
			y = toInt(pointF.y);
		}

		logger.log('Start point: (' + x + '; ' + y + ')');

		while (x < matrix.sizeX && point == null) {
			point = matrix.searchForFirstEmpty(x, 0, 0, 1);
			if (point != null) {
				point = matrix.searchForFreeRect(
					point.x, point.y, 0, 1,
					toInt(width),   toInt(height),
					toInt(marginX), toInt(marginY));
				//better than by radius
			}
			x += 8; //magic number =/
			y  = 0;
		}

		if (point == null) {
			logger.log("There is no space to put widget");
		} else {
			addWidget(
				point.x, point.y,
				width, height, widget);
			cacheSize(
				width, height,
				point.x, point.y);
			logger.log('Free point is ');
			logger.logAppend('(' + point.x + ',' + point.y + ')');
			logger.indent--;
		}
	}

	public function setAutomatically(
		x : Float, y : Float,
		widget : Widget) {

		automatic.add(
			addAutomatically(
				x,y, widget));
	}

	function addAutomatically(
		x : Float, y : Float,
		widget : Widget) : Layout.Item {

		logger.log('Automatic insertion:');
		logger.indent++;

		logger.log('First free point is ');
		var pl = matrix.searchForLastEmpty(toInt(x), toInt(y), -1, 0);
		checkNull(pl);
		var pt = matrix.searchForLastEmpty(toInt(x), toInt(y),  0,-1);
		checkNull(pt);
		var x1 = pl.x;
		var y1 = pt.y;
		logger.logAppend('(' + x1 + ',' + y1 + ')');

		logger.log('Second free point is ');
		var pr = matrix.searchForLastEmpty(toInt(x), toInt(y),  1, 0);
		checkNull(pr);
		var x2 = pr.x;
		var pb = matrix.searchForLastEmpty(toInt(x), toInt(y),  0, 1);
		checkNull(pb);
		var y2 = pb.y;
		logger.logAppend('(' + x2 + ',' + y2 + ')');

		logger.indent--;
		var item : Layout.Item = {
			x     :toFloat(x1),
			y     :toFloat(y1),
			width :toFloat((x2 - x1 + 1)),
			height:toFloat((y2 - y1 + 1)),
			widget:widget
		};
		addItem(item);
		return item;
	}

	function checkNull(point : {x : Int, y : Int}) {
		if (point == null) {
			logger.log("Cannot place widget here.");
		}
	}

	function updateAutomatic() {
		for (item in automatic) {
			removeWidget(item.widget);
			addAutomatically(
				item.x, item.y, item.widget);
		}
	}

	override
	public function addItem(item : Layout.Item) {
		matrix.setRect(
			toInt(item.x),
			toInt(item.y),
			toInt(item.width),
			toInt(item.height),
			item);
		super.addItem({
			x      : floor(item.x),
			y      : floor(item.y),
			width  : item.width,
			height : item.height,
			widget : item.widget
		});
	}

	override
	public function removeItem(item : Layout.Item) {

		//cleaning cache
		cachedSizes = new List<CachedSizeEnty>();

		automatic.remove(item);
		matrix.setRect(
			toInt(item.x),
			toInt(item.y),
			toInt(item.width),
			toInt(item.height),
			null);
		super.removeItem({
			x      : floor(item.x),
			y      : floor(item.y),
			width  : item.width,
			height : item.height,
			widget : item.widget
		});
	}

	static function tan(
		x1 : Float, y1 : Float,
		x2 : Float, y2 : Float) {

		return (y2 - y1) / (x2 - x1);
	}
	static function toInt(value : Float) : Int {
		return Math.floor(value);
	}
	static function toFloat(value : Int) : Float {
		return cast(value, Float);
	}
	static function floor(value : Float) : Float {
		return toFloat(Math.floor(value));
	}

	//todo: create map class and remove it from here

	function getCachedSize(width : Float, height : Float) : {x : Float, y : Float} {
		//copypaste =/
		for (entry in cachedSizes) {
			if (entry.width == width && entry.height == height) {
				return {x : entry.x , y : entry.y};
			}
		}
		return null;
	}

	function cacheSize(
		width : Float, height : Float,
		x     : Float, y      : Float) {

		var createNew = true;
		for (entry in cachedSizes) {
			if (entry.width == width && entry.height == height) {
				createNew = false;
				entry.x   = x;
				entry.y   = y;
				break;
			}
		}
		if (createNew) {
			cachedSizes.add({
				width : width,
				height : height,
				x : x, y : y
			});
		}
	}
}
