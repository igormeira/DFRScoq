#!/bin/sh

echo "Compiling *.v files" ;
coq_makefile -f Make -o Makefile ;
make ;
echo "Compilation completed"
