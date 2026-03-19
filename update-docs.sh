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
	cd "$BASE_DIR/projects/LCS
	lake build LCS:literate
	lake exe verso-html .lake/build/literate ../../docs/source
else 
	echo "Skipping Interactive Source generation."
fi


echo "Done! Docs are updated."
