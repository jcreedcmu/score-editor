watch:
	node build.js watch

serve:
	cd public && python3 -m http.server 8000

check:
	npx tsc -w
