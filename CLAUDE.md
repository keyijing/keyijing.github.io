# CLAUDE.md

## Project Overview

Jekyll-based personal academic homepage for GitHub Pages (`keyijing.github.io`). See `README.md` for full architecture, file structure, and styling details.

## Coding Guidance

- Prefer editing existing files over creating new ones.
- Keep prose in Markdown (`index.md`); structured data (education, awards, research) in `_data/homepage.yml`.
- Use `_includes/inline-md.html` for inline Markdown rendering in YAML text fields.
- Use `_data/homepage.yml` for all author info: name, pronunciation, bio (title/institution in Markdown), and contacts.
- Use SCSS variables (`$primary`) and CSS custom properties (`--primary`) for colors; keep them in sync.
- Primary color `#0070f3` is for links only — not headings. Sidebar bio links inherit text color and only highlight on hover.
- Load icons via CDN (Font Awesome 6 + Academicons); don't bundle icon fonts locally.
- All links open in new tabs via `<base target="_blank">` in `default.html`.
- KaTeX is loaded for math rendering (`$...$`, `$$...$$`, `\(...\)`, `\[...\]`).
- Research entries support a `links` array (icon + text + url) for paper links (PDF, arXiv, OpenReview, etc.).

## Pre-commit Checklist

- **Always update `README.md` and `CLAUDE.md`** to reflect any structural or architectural changes before committing.

## Build

```bash
bundle exec jekyll build    # build
bundle exec jekyll serve    # local dev server at localhost:4000
```

Uses the `github-pages` gem for GitHub Pages compatibility.
