define(['codemirror/addon/mode/simple', "base/js/namespace", 'codemirror/lib/codemirror'], function (cmsm, IPython, CodeMirror) {

  load_mode = function () {
    console.log("tlaplus kernel.js loaded");

    CodeMirror.defineSimpleMode("tlaplus", {
      start: [
        // The regex matches the token, the token property contains the type
        { regex: /"(?:[^\\]|\\.)*?(?:"|$)/, token: "string" },

        // You can match multiple tokens at once. Note that the captured
        // groups must span the whole string in this case
        { regex: /(\w+)\s*(?:\([^\)]*\))?\s*(==)/, token: ["keyword", "operator"] },

        // Rules are matched in the order in which they appear, so there is
        // no ambiguity between this one and the one above
        {
          regex: /(?:ACTION|ASSUME|ASSUMPTION|AXIOM|BY|CASE|CHOOSE|CONSTANT|CONSTANTS|COROLLARY|DEF|DEFINE|DEFS|DOMAIN|ELSE|ENABLED|EXCEPT|EXTENDS|HAVE|HIDE|IF|IN|INSTANCE|LET|LAMBDA|LEMMA|LOCAL|MODULE|NEW";, "OBVIOUS|OMITTED|ONLY|OTHER|PICK|PROOF|PROPOSITION|PROVE|QED|RECURSIVE|SF_|STATE|SUFFICES|SUBSET|TAKE|TEMPORAL|THEN|THEOREM|UNCHANGED|UNION|USE|VARIABLE|VARIABLES|WF_|WITH|WITNESS)\b/,
          token: "keyword"
        },
        { regex: /TRUE|FALSE|\\E|\\in|\\A/, token: "atom" },
        { regex: /0x[a-f\d]+|[-+]?(?:\.\d+|\d+\.?\d*)(?:e[-+]?\d+)?/i, token: "number" },
        { regex: /\/(?:[^\\]|\\.)*?\//, token: "variable-3" },

        // comments
        { regex: /\\\*.*/, token: "comment" },
        { regex: /\(\*/, token: "comment", next: "comment" },
        { regex: /[-+\/\\*=<>!]+/, token: "operator" },

        // // indent and dedent properties guide autoindentation
        // {regex: /[\{\[\(]/, indent: true},
        // {regex: /[\}\]\)]/, dedent: true},
        // {regex: /[a-z$][\w$]*/, token: "variable"},
      ],

      // The multi-line comment state.
      comment: [
        { regex: /.*?\*\)/, token: "comment", next: "start" },
        { regex: /.*/, token: "comment" }
      ],

      // The meta property contains global information about the mode. It
      // can contain properties like lineComment, which are supported by
      // all modes, and also directives like dontIndentStates, which are
      // specific to simple modes.
      meta: {
        dontIndentStates: ["comment"],
        lineComment: '\*'
      }
    });

    CodeMirror.defineMIME("text/x-tlaplus", "tlaplus");

    // assorted kludges to deal with fact that all this stuff can be loaded
    // after full notebook init
    IPython.CodeCell.options_default["cm_config"]["mode"] = "tlaplus";
    [...document.querySelectorAll('.code_cell .CodeMirror')].forEach(c => {
      c.CodeMirror.setOption('mode', 'tlaplus');
    });
    Jupyter.notebook.get_cells().forEach(c => {
      c._options.cm_config['mode'] = 'tlaplus';
    });
  }

  return {
    onload: function () {
      // setTimeout(load_mode, 3000);
      load_mode();
    }
  }
});
