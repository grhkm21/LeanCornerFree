all:
	mkdir -p build
	# lualatex --shell-escape -draftmode --interaction=nonstopmode -output-directory=build main.tex
	# biber --input-directory=build main
	lualatex --shell-escape --interaction=nonstopmode -output-directory=build main.tex
	ln -sf build/main.pdf .
