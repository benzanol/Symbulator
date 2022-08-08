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


// Format all elements with class 'mq-static' as latex equations
function formatStaticEquations() {
    var spans = document.getElementsByClassName('mq-static');
    for (let i = 0; i < spans.length; i++) {
        MQ.StaticMath(spans[i]);
    }
}
