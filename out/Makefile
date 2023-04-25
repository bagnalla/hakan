js: out.js
	node out.js

asm: out.c
	gcc -S -fno-asynchronous-unwind-tables -O2 out.c -no-pie gc.a

c: out.c
	gcc -g out.c -no-pie gc.a
	./a.out

clean:
	rm -f out.js out.c a.out out.mal
