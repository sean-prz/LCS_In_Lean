#!/bin/bash

BASE_DIR=$(pwd)

# 1. Generate the docs
echo "Generating manual"
cd "$BASE_DIR/projects/docs_LCS"
lake exe generate-docs

cp -r _out/html-multi/* "$BASE_DIR/docs/"


read -p "Do you want to generate the Interactive Source? (it's quite long) [y/N]: " response
if [[ "$response" =~ ^([yY][eE][sS]|[yY])$ ]]
then
	# 2. Generate the interactive source
	echo "Generating Interactive Source"
	cd "$BASE_DIR/projects/LCS"
	lake build LCS:literate
	lake exe verso-html .lake/build/literate ../../docs/source
else 
	echo "Skipping Interactive Source generation."
fi


echo "Done! Docs are updated."

# 3. Build doc4
read -p "Do you want to build doc4  [y/N]: " doc_response
if [[ "$doc_response" =~ ^([yY][eE][sS]|[yY])$ ]]
then
	echo "Building doc4"
	cd "$BASE_DIR/projects/LCS/docbuild"
	lake build LCS:docs
	cp -r .lake/build/doc "$BASE_DIR/postprocess_docs/source"
	cd "$BASE_DIR/postprocess_docs"
	.venv/bin/python3 main.py
	cp -r source/doc/. "$BASE_DIR/docs/doc4"
fi

# 4. Compile status.typ
echo "Compiling status report"
cd "$BASE_DIR/typst"
typst compile status.typ
mv status.pdf "$BASE_DIR/docs/status.pdf"


# 5. Serve the docs
read -p "Do you want to serve the docs at http://localhost:8004? [y/N]: " serve_response
if [[ "$serve_response" =~ ^([yY][eE][sS]|[yY])$ ]]
then
	echo "Serving docs at http://localhost:8004..."
	# Ensure we are in the base directory where the 'docs' folder is
	cd "$BASE_DIR"
	python3 -m http.server 8004 -d docs
fi
