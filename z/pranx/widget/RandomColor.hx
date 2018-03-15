package widget;

class RandomColor {
	private function new() {}
	public static function withMask(
		mask : Int, value : Int) {
		return   (mask             & value) + 
				((mask ^ 0xFFFFFF) & full());
	}
	public static function full() {
		return Std.random(0x1000000);
	}
}
