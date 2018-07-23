const from_polar = function(angle, radius) {
    return {
        x: radius * Math.cos(angle),
        y: radius * Math.sin(angle)
    };
};

const polygon = function(n) {
    let result = [];
    let angle = 2 * Math.PI / n;
    for (let i = 0; i < n; i++) {
        const point = from_polar(i * angle, 1);
        result.push(point.x);
        result.push(point.y);
    }
    return result;
};

const move_2d = function(points, v) {
    return points.map((from, i) => {
        if (i % 2 === 0) {
            return from + v.x;
        } else {
            return from + v.y;
        }
    });
};

const stretch_2d = function(points, q) {
    return points.map((from, i) => {
        if (i % 2 === 0) {
            return from * q.x;
        } else {
            return from * q.y;
        }
    });
};

const triangulate_2d = function(contour, z, rgb) {
    let n = contour.length;
    if (n < 6) {
        alert("Can't triangulate " + n / 2 + " vertices");
        return undefined;
    }

    let r = rgb[0];
    let g = rgb[1];
    let b = rgb[2];

    let center = {x: 0, y: 0};
    for (let i = 0; i < n; i += 2) {
        center = {
            x: center.x + contour[i],
            y: center.y + contour[i+1]
        };
    }
    center = {
        x: 2 * center.x / n,
        y: 2 * center.y / n
    };

    let result = [];
    for (let i = 0; i < n - 2; i += 2) {
        result = result.concat([
            contour[i], contour[i+1],     z, r, g, b,
            contour[i+2], contour[i+3],   z, r, g, b,
            center.x, center.y,           z, r, g, b
        ]);
    }
    result = result.concat([
        contour[n-2], contour[n-1],       z, r, g, b,
        contour[0], contour[1],           z, r, g, b,
        center.x, center.y,               z, r, g, b
    ]);

    return new Float32Array(result);
};