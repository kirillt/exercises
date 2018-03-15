package layout;

import log.Logger;

class Matrix<T> {

	var matrix : Array<Array<T>>;
	var logger : Logger;

	public var sizeX(default,setSX) : Int;
	public var sizeY(default,setSY) : Int;

	function setSX(sx : Int) {
		logger.log('Size X: ' + sx);
		sizeX = sx;
		return sx;
	}
	function setSY(sy : Int) {
		logger.log('Size Y: ' + sy);
		sizeY = sy;
		return sy;
	}

	public function new(
		logger : Logger) {

		this.logger = logger;

		this.sizeX  = 0;
		this.sizeY  = 0;

		this.matrix = new Array();
	}

	public function searchForLastEmpty(
		x1 : Int, y1 : Int,
		dx : Int, dy : Int) {

		return moveWhile(
			true,
			x1, y1, dx, dy,
			function(x : Int, y : Int, t : T) {
				return t == null;
			});
	}

	public function searchForFirstEmpty(
		x1 : Int, y1 : Int,
		dx : Int, dy : Int) {

		return moveWhile(
			false,
			x1, y1, dx, dy,
			function(x : Int, y : Int, t : T) {
				return t != null;
			});
	}

	public function searchForFreeRect(
		x1 : Int, y1 : Int,
		dx : Int, dy : Int,
		width   : Int,
		height  : Int,
		marginX : Int,
		marginY : Int) {

		return moveWhile(
			false,
			x1, y1, dx, dy,
			function(x : Int, y : Int, t : T) {
				if (x + width + 2*marginX > sizeX + 1 || y + height + 2*marginY > sizeY + 1) {
					return true;
				}

				return !isFreeRect(
					x - marginX,
					y - marginY,
					width  + 2*marginX,
					height + 2*marginY);
			});
	}

	public function moveWhile(
		returnPrevNotLast : Bool,
		x1 : Int, y1 : Int,
		dx : Int, dy : Int,
		predicate) {

		logger.log('Moving from ('  + x1 + ',' + y1 + ').');
		logger.log('Direction is (' + dx + ',' + dy + ').');

		if (!inBounds(x1,y1)) {
			logger.log('Start point is out of bounds. Null is returned.');
			return null;
		}
		logger.indent++;

		var prevX = x1;
		var prevY = y1;
		var currX = x1;
		var currY = y1;

		while (
			predicate(
				currX,currY,
				getPoint(currX, currY)) &&
			inBounds(currX,currY)) {

			prevX  = currX;
			prevY  = currY;
			currX += dx;
			currY += dy;
		}

		var resultX;
		var resultY;
		if (returnPrevNotLast) {
			logger.log('Required last point satisfied predicate.');
			resultX = prevX;
			resultY = prevY;
		} else {
			logger.log('Required first point not satisfied predicate.');
			resultX = currX;
			resultY = currY;
		}

		logger.log('Result point is (' + resultX + ',' + resultY + ')');
		if (!inBounds(resultX, resultY)) {
			logger.log('Result point is out of bounds. Null is returned.');
			logger.indent--;
			return null;
		} else {
			logger.indent--;
			return {x:resultX, y:resultY};
		}
	}

	public function getPoint(x : Int, y : Int) : T {
		if (inBounds(x, y)) {
			return matrix[x][y];
		} else {
			return null;
		}
	}
	public function getRect(
		x     : Int, y       : Int,
		width : Int, height : Int) : Iterator<T> {

		var set = new Hash<T>();

		//todo: remove copy-paste
		//todo: rectangle intersection
		var left   = x < 0 ? 0 : x;
		var right  = x + width  > sizeX ? sizeX : x + width;
		var top    = y < 0 ? 0 : y;
		var bottom = y + height > sizeY ? sizeY : y + height;

		for (i in left...right) {
			for (j in top...bottom) {
				set.set("", matrix[i][j]);
			}
		}
		return set.iterator();
	}

	public function isFreeRect(
		x     : Int, y      : Int,
		width : Int, height : Int) : Bool {

		//todo: remove copy-paste
		//todo: rectangle intersection
		var left   = x < 0 ? 0 : x;
		var right  = x + width  > sizeX ? sizeX : x + width;
		var top    = y < 0 ? 0 : y;
		var bottom = y + height > sizeY ? sizeY : y + height;

		for (i in left...right) {
			for (j in top...bottom) {
				if (matrix[i][j] != null) {
					return false;
				}
			}
		}
		return true;
	}

	public function setPoint(x : Int, y : Int, t : T) {
		expand(x + 1, y + 1);
		matrix[x][y] = t;
	}
	public function setRect(
		x     : Int, y       : Int,
		width : Int, height : Int,
		t : T) {

		expand(x + width, y + height);
		for (i in x...x + width) {
			for (j in y...y + height) {
				matrix[i][j] = t;
			}
		}
	}

	function expand(sizeX : Int, sizeY : Int) {
		if (!inBounds(sizeX - 1, sizeY - 1)) {
			for (i in this.sizeX...sizeX) {
				matrix[i] = new Array();
			}
			this.sizeX = sizeX > this.sizeX ? sizeX : this.sizeX;
			this.sizeY = sizeY > this.sizeY ? sizeY : this.sizeY;
		}
	}

	function inBounds(x : Int, y : Int) {
		return  x < this.sizeX &&
				y < this.sizeY &&
				x > -1 &&
				y > -1;
	}
}
