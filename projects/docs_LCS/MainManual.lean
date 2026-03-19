import Std.Data.HashMap
import VersoManual

import DocsLCS.Docs 
import DocsLCS.Section1
open Verso Doc
open Verso.Genre Manual

open Std (HashMap)
open DocsLCS.Docs


def smallHead : CSS := ".header-title h1 { font-size: 20px; }"
def CodeCSS : CSS := "code { font-family: var(--verso-code-font-family); color: var(--verso-code-color); background: #f4f4f4; padding: 0.2em 0.4em; border-radius: 3px; font-size: 0.9em; }"



def config : RenderConfig where
  emitTeX := false
  htmlDepth := 1
  emitHtmlSingle := .immediately
  extraCss := {smallHead, CodeCSS} 


def main := manualMain (%doc DocsLCS.Docs) (config := config)
