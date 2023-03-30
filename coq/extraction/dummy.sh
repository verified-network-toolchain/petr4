#!/bin/sh
if [ "$*" = "coq/extraction/V1ModelTarget.mli" ]; then
  cat $* | sed "s#('a1, 'a2) coq_ExternSem#(__, __) coq_ExternSem#" \
         | sed "s#('a1, 'a2) coq_Target#(__, __) coq_Target#"
else
  cat $*
fi
