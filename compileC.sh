echo "Typechecking and compiling..."
stack build --allow-different-user && stack exec --allow-different-user hakan-exe $1 c out/out.c
# cd out
# echo "Minifying..."
# cp out.js out_temp.js
# java -jar closure_compiler.jar --warning_level=QUIET --js out_temp.js --js_output_file out.js
# rm out_temp.js
# echo "Program output:"
# make js
