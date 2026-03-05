# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Personal academic homepage for David Pichardie (`https://davidpichardie.github.io`). Purely static site — hand-written HTML and CSS, no JavaScript, no build system, no static site generator. Deployed via GitHub Pages from `master`.

## Site Structure

- **Top-level HTML pages**: `index.html` (home/bio/activities), `research.html`, `publi.html` / `publi_abstracts.html` / `publi_bib.html` (publications), `teaching.html`
- **Single stylesheet**: `style.css` (shared by all pages)
- **Static assets**: `img/` (photos/icons), `papers/` (research PDFs), `talks/` (slides)
- **Teaching materials**: `teaching/` tree organized by level (`L3/`, `M1/`, `M2/`) and events, containing PDFs, OCaml `.ml` files, and Coq `.v` files
- **ERC project page**: `erc/index.html`

## Key Architecture Details

- **No templating**: Navigation sidebar is manually duplicated across each top-level HTML page. When updating the nav menu, all pages must be edited.
- **Character encoding**: Pages use `iso-8859-1` (XHTML 1.0 Transitional). New content must use compatible characters or HTML entities.
- **Publications workflow**: The three `publi*.html` files are generated offline from `publi.bib` using an external tool (likely `bibtex2html`). Edit `publi.bib` and regenerate rather than editing the HTML directly.
- **CSS origin**: Layout based on a template by James Koster (OSWD), adapted from Xavier Leroy's homepage.
