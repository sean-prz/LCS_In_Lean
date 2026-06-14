#!/bin/bash

BASE_DIR=$(pwd)
# 1. Build doc4
echo "Building doc4"
cd "$BASE_DIR/src/docbuild"
lake build LCS:docs
cp -r .lake/build/doc "$BASE_DIR/postprocess_docs/source"
cd "$BASE_DIR/postprocess_docs"
.venv/bin/python3 main.py
cp -r source/doc/. "$BASE_DIR/docs/documentation"

# 2. Compile.typ
echo "Compiling status report"
cd "$BASE_DIR/report"
typst compile main.typ
mv main.pdf "$BASE_DIR/docs/report.pdf"


# 3. Take the source files to the docs folder for reference
cp "$BASE_DIR/postprocess_docs/source/index.html" "$BASE_DIR/docs/index.html"
cp "$BASE_DIR/postprocess_docs/source/CNAME" "$BASE_DIR/docs/CNAME"


# 4. Cleanup (remove source files)
rm -rf "$BASE_DIR/postprocess_docs/source/doc"/*

# 5. Serve the docs
read -p "Do you want to serve the docs at http://localhost:8004? [y/N]: " serve_response
if [[ "$serve_response" =~ ^([yY][eE][sS]|[yY])$ ]]
then
	echo "Serving docs at http://localhost:8004..."
	# Ensure we are in the base directory where the 'docs' folder is
	cd "$BASE_DIR"
	python3 -m http.server 8004 -d docs
fi
