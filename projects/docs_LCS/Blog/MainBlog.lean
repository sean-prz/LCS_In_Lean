import VersoBlog
import Docs.Blog -- Importing your Blog file

open Verso Genre Blog Site Theme Syntax

-- Define a tiny site where your post is the front page
def mySite : Site := site Docs.Blog /
  static "static" ← "static_files"


-- The main runner using Verso's default theme
def main := blogMain Theme.default mySite
