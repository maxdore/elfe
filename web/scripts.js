window.onload = function () {
    new Vue({
        el: '.prover',
        data: {
            input: "",
            output: "",
            submitted: true,
            unchangedSince: new Date()
        },
        methods: {
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
                        console.log(response.body);
                        if (response.body.tag == "NotParsed") {
                            this.output = "Parsing error:\n" + response.body.contents;
                        } else {
                            this.output = "The text is " + response.body.contents.toLowerCase();
                        }

                        
                    }, response => {
                        this.output = response.body;
                });

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