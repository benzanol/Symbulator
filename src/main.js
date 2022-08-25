// Set up mathquill
const MQ = MathQuill.getInterface(2);

function makeMQField(elem, onChange) {
    MQ.MathField(elem, {
        handlers: {
            edit: (field) => {
                const eqn_elem = field.__controller.container.context;
                onChange(MQ(eqn_elem).latex());
            }
        }
    });
}


// Format all latex equation with katex
function katexFormatElement(element, latex) {
    katex.render(latex, element, { throwOnError: false });
}


var tickTimer = null
function tickCalculator(call) {
    // Kill any existing tick timer
    clearTimeout(tickTimer)
    //console.log('Ticking - ' + tickTimer)

    if (call()) {
        tickTimer = setTimeout(() => tickCalculator(call), 0);
    } else {
        //console.log('Stopped ticking')
    }
}


function createDiagonalPattern(color = 'black') {
    // create a 10x10 px canvas for the pattern's base shape
    let shape = document.createElement('canvas')
    let c = shape.getContext('2d')
    let [w, h] = [12, 12]
    shape.width = w
    shape.height = h

    c.lineWidth = 3

    console.log(color)
    // draw 1st line of the shape 
    c.strokeStyle = color

    c.beginPath()
    // Top left to bottom right
    c.moveTo(-0.5*w, 0)
    c.lineTo(w, 1.5*h)
    c.moveTo(0, -0.5*h)
    c.lineTo(1.5*w, h)

    // Bottom left to top right
    c.moveTo(-0.5*w, h)
    c.lineTo(w, -0.5*h)
    c.moveTo(0, 1.5*h)
    c.lineTo(1.5*w, 0)

    c.stroke()
    // create the pattern from the shape
    return c.createPattern(shape, 'repeat')
}
