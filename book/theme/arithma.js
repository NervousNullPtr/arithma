window.addEventListener("load", function () {
  if (typeof hljs === "undefined") return;

  if (!hljs.getLanguage("arithma")) {
    hljs.registerLanguage("arithma", function (hljs) {
      return {
        name: "arithma",
        keywords: {
          literal: "true false i",
          built_in: "sin cos tan sqrt ln log abs conj print assert",
        },
        contains: [
          hljs.COMMENT("//", "$"),
          hljs.C_NUMBER_MODE,
          hljs.QUOTE_STRING_MODE,
          { className: "keyword", begin: /\b(if|else|for|assert|in)\b/ },
          { className: "function", begin: /\b[a-zA-Z_][a-zA-Z0-9_]*\s*(?=\()/ },
          { className: "operator", begin: /[+\-*/^=!<>|&]+/ },
        ],
      };
    });
  }

  document.querySelectorAll("pre code.language-arithma").forEach(block => {
    const result = hljs.highlight("arithma", block.textContent, true);
    block.innerHTML = result.value;
    block.classList.add("hljs");
  });
});