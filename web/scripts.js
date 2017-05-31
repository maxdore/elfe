window.onload = function () {
    var v = new Vue({
        el: '.prover',
        data: {
            input: `Notation relapp: R[x,y].

Let relation(R).

Lemma: transitive(R) and symmetric(R) implies R is reflexive.
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
            autoSubmit: false,
            loading: false,
            unchangedSince: new Date(),
            row: 0,
            col: 0,
            errorLines: [],
        },
        methods: {
            initEditor: function(){
                for (var i = 1; i <= 20; i++) {
                    $('.linewrapper').append('<div class="line" id="line' + i + '"><div class="number">' + i + '</div></div>');
                }
            },

            submit: function(){
                this.loading = true;
                this.$http.get('/api', {params: {problem: this.input}}).then(response => {
                        this.result = response.body.contents;
                        console.log(this.result);
                        this.errorLines = [];

                        if (response.body.tag == "NotParsed") {
                            this.output = "Parsing error:\n" + this.result;
                            if (/^\d+$/.test(this.result.substr(6,2))) {
                                var line = this.result.substr(6,2);
                            } else {
                                var line = this.result.substr(6,1);
                            }
                            this.errorLines.push(line);
                        } else {
                            this.output = "Verified";
                            this.result.map(this.updateLines);
                        }
                        this.renderLines();
                        this.loading = false;
                    }, response => {
                        this.output = "There was an error!\n";
                        this.output += response.body;
                        this.loading = false;
                });
            },
            findResultToPos: function(){
                if (this.result instanceof Array) {
                    this.result.map(this.objectInPos);
                }
            },
            objectInPos: function(obj){
                if (obj.opos.tag != "None") {
                    var row = obj.opos.contents[0];
                    var col = obj.opos.contents[1];
                    if (row == this.row) {
                        console.log(obj);
                        if (obj.status.tag == "Correct") {
                            this.output = obj.status.tag;
                            this.output += "\n\nRaw formula: " + obj.sformula;
                        }
                        else if (obj.status.tag == "Incorrect") {
                            this.output = "Disproved by " 
                                            + obj.status.contents.contents[0]
                                            + ".\nCountermodel: \n"
                                            + obj.status.contents.contents[1];
                            this.output += "\nRaw formula: " + obj.sformula;
                        }
                    }
                }
                if (obj.children instanceof Array) {
                    obj.children.map(this.objectInPos);
                }
            },
            updateLines: function(obj){
                if (obj.opos.tag != "None") {
                    var row = obj.opos.contents[0];
                    var col = obj.opos.contents[1];
                    if (obj.status.tag == "Correct") {
                    }
                    else if (obj.status.tag == "Incorrect") {
                        this.errorLines.push(row);
                    }
                }
                if (obj.children.length > 0) {
                    obj.children.map(this.updateLines);
                }
            },
            renderLines: function(){
                numRows = this.input.split("\n").length;
                $('.linewrapper').html('');
                for (var i = 1; i <= numRows; i++) {
                    $('.linewrapper').append('<div class="line" id="line' + i + '"><div class="number">' + i + '</div></div>');
                }

                $('.line').addClass('correct');
                for (var i = 0; i < this.errorLines.length; i++) {
                    $('#line'+this.errorLines[i]).removeClass('correct');
                    $('#line'+this.errorLines[i]).addClass('error');
                }

                pos = $('#input').prop('selectionStart');
                textUntilPos = this.input.substr(0, pos);
                this.row = textUntilPos.split("\n").length;
                $('.line').removeClass('active');
                $('#line'+this.row).addClass('active');
                this.col = textUntilPos.substr(textUntilPos.lastIndexOf("\n")).length;
                this.findResultToPos();
            },

            renderLinesPos: function(){
                o = $("#input").prop('scrollTop');
                $('.linewrapper').css('top', 42 - o);
            },
            insertKey: function(key) {
                pos = $('#input').prop('selectionStart');
                this.input = this.input.slice(0, pos) + key + this.input.slice(pos);
                $('#input').prop('selectionStart', 10);
                $('#input').prop('selectionEnd', 15);
                $('#input').focus();
            }
        }
    });
    v.initEditor();
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
  if ((keyCode == 13 && e.ctrlKey) || (keyCode == 83 && e.ctrlKey)) {
    e.preventDefault();
    $('#verifyButton').click();
  }

});


