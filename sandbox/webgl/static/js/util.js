function flatten(arr, result = []) {
    for (let i = 0, length = arr.length; i < length; i++) {
        const value = arr[i];
        if (Array.isArray(value)) {
            flatten(value, result);
        } else {
            result.push(value);
        }
    }
    return result;
}

function concatenate(Constructor, arrays) {
    const totalLength = arrays.reduce((total, arr) => {
        return total + arr.length
    }, 0);
    const result = new Constructor(totalLength);
    arrays.reduce((offset, arr) => {
        result.set(arr, offset);
        return offset + arr.length;
    }, 0);
    return result;
}

function random_color() {
    return [Math.random(), Math.random(), Math.random()];
}

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}