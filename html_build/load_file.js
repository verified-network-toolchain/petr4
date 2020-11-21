onmessage = function (e) {
  var code_file = new XMLHttpRequest();
  code_file.open("GET", "p4/" + e.data[0], false);
  code_file.send();
  var text = code_file.responseText;
  console.log("request done");
  postMessage(text);
}
