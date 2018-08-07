function bindLastArgs(func, ...boundArgs) {
    return function (...baseArgs) {
        return func(...baseArgs, ...boundArgs);
    }
}

window.js = {};

function grayscale(data) {
    for (let i = 0; i < data.length; i+= 4) {
        data[i+1] = data[i];
        data[i+2] = data[i];
    }
    return data;
}

function negative(data) {
    for (let i = 0; i < data.length; i+= 4) {
        data[i]   = 255 - data[i];
        data[i+1] = 255 - data[i+1];
        data[i+2] = 255 - data[i+2];
    }
    return data;
}

window.js.grayscale = grayscale;
window.js.negative = negative;

function multiFilter(data, width, filterType, mag, mult, adj) {
    for (let i = 0; i < data.length; i += filterType) {
        if (i % 4 !== 3) {
            data[i] = mag + mult * data[i] - data[i + adj] - data[i + width * 4];
        }
    }
    return data;
}

const sunset   = bindLastArgs(multiFilter, 4, 127, 2, 4);
const forest   = bindLastArgs(multiFilter, 5, 127, 3, 1);
const longhorn = bindLastArgs(multiFilter, 2, 27,  3, 2);

window.js.longhorn = longhorn;
window.js.sunset = sunset;
window.js.forest = forest;

function convFilter(data, width, height, kernel, divisor, bias=0, count=1) {
    const w = kernel[0].length;
    const h = kernel.length;
    const half = Math.floor(h / 2);
    for (let i = 0; i < count; i += 1) {
        for (let y = 1; y < height - 1; y += 1) {
            for (let x = 1; x < width - 1; x += 1) {
                const px = (y * width + x) * 4;  // pixel index
                let r = 0, g = 0, b = 0;

                for (let cy = 0; cy < h; ++cy) {
                    for (let cx = 0; cx < w; ++cx) {
                        const cpx = ((y + (cy - half)) * width + (x + (cx - half))) * 4;
                        r += data[cpx + 0] * kernel[cy][cx];
                        g += data[cpx + 1] * kernel[cy][cx];
                        b += data[cpx + 2] * kernel[cy][cx];
                    }
                }

                data[px + 0] = (1 / divisor) * r + bias;
                data[px + 1] = (1 / divisor) * g + bias;
                data[px + 2] = (1 / divisor) * b + bias;
                }
            }
        }
    return data;
}

const blur = bindLastArgs(convFilter, [[1, 1, 1], [1, 1, 1], [1, 1, 1]], 9, 0, 3);
const goodMorning = bindLastArgs(convFilter, [[-1, -1, 1], [-1,  14, -1], [1, -1, -1]], 3);

window.js.goodMorning = goodMorning;
window.js.blur = blur;