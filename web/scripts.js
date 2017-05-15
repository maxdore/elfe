window.onload = function () {
    new Vue({
        el: '.prover',
        data: {
            input: `Notation relapp: R[x,y].

Let relation(R).

Lemma: transitive(R) and symmetric(R) and bound(R) implies R is reflexive.
Proof:
    Assume transitive(R) and symmetric(R) and bound(R).
    Assume x is element.
    Take y such that element(y) and R[x,y] by boundness.
    Then R[y,x] by symmetry.
    Hence R[x,x] .
    Hence R is reflexive.
qed.`,
            output: "",
            result: {},
            submitted: true,
            unchangedSince: new Date(),
            row: 0,
            col: 0
        },
        methods: {
            cursorChanged: function(){
                pos = $('#input').prop('selectionStart');
                textUntilPos = this.input.substr(0, pos);
                this.row = textUntilPos.split("\n").length;
                this.col = textUntilPos.substr(textUntilPos.lastIndexOf("\n")).length;
                this.findResultToPos();
            },
            inputChanged: function(){
                this.submitted = false;
                this.unchangedSince = new Date(); 
                setTimeout(this.submit, 1000);
            },
            submit: function(){
                var now = new Date();
                if (this.submitted || (now.getTime() - this.unchangedSince.getTime()) < 1000) {
                    return;
                }
                this.submitted = true;
                console.log("called now");
                this.output = "Loading...";
                this.$http.get('/api', {params: {problem: this.input}}).then(response => {
                        this.result = response.body.contents;
                        console.log(this.result);
                        if (response.body.tag == "NotParsed") {
                            this.output = "Parsing error:\n" + response.body.contents;
                        } else {
                            this.output = "???";
                        }
                    }, response => {
                        this.output = response.body;
                });
            },
            findResultToPos: function(){
                this.result.map(this.objectInPos);
            },
            objectInPos: function(obj){
                if (obj.opos.tag != "None") {
                    row = obj.opos.contents[0];
                    col = obj.opos.contents[1];
                    if (row == this.row) {
                        console.log(obj);
                        this.output = obj.sformula + "\n";
                        if (obj.status.tag == "Correct") {
                            this.output = obj.status.tag;
                        }
                        else if (obj.status.tag == "Incorrect") {
                            this.output += "Disproved by " 
                                            + obj.status.contents.contents[0]
                                            + ".\n Countermodel: \n"
                                            + obj.status.contents.contents[1];
                        }
                    }
                }
                if (obj.children.length > 0) {
                    obj.children.map(this.objectInPos);
                }
            }
        }
    })
}

$(document).delegate('.input', 'keydown', function(e) {
  var keyCode = e.keyCode || e.which;

  if (keyCode == 9) {
    e.preventDefault();
    var start = $(this).get(0).selectionStart;
    var end = $(this).get(0).selectionEnd;

    // set textarea value to: text before caret + tab + text after caret
    $(this).val($(this).val().substring(0, start)
                + "    "
                + $(this).val().substring(end));

    // put caret at right position again
    $(this).get(0).selectionStart =
    $(this).get(0).selectionEnd = start + 4;
  }
});