# CLAUDE.md

## Project Overview

Jekyll-based personal academic homepage for GitHub Pages (`keyijing.github.io`). See `README.md` for full architecture, file structure, and styling details.

## Coding Guidance

- Prefer editing existing files over creating new ones.
- Keep content in Markdown (`index.md`); layout and styling stay separate.
- Use `_data/homepage.yml` for author name/contacts; use `_includes/sidebar-bio.md` for title/institution.
- Use SCSS variables (`$primary`) and CSS custom properties (`--primary`) for colors; keep them in sync.
- Primary color `#0070f3` is for links only — not headings. Sidebar bio links inherit text color and only highlight on hover.
- Load icons via CDN (Font Awesome 6 + Academicons); don't bundle icon fonts locally.

## Build

```bash
bundle exec jekyll build    # build
bundle exec jekyll serve    # local dev server at localhost:4000
```

Uses the `github-pages` gem for GitHub Pages compatibility.
