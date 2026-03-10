import VersoBlog
import TestLCS.Blog -- Importing your Blog file

open Verso Genre Blog Site Theme Syntax

-- Define a tiny site where your post is the front page
def mySite : Site := site TestLCS.Blog
-- The main runner using Verso's default theme
def main := blogMain Theme.default mySite
