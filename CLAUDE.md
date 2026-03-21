# CLAUDE.md

## Project Overview

Jekyll-based personal academic homepage for GitHub Pages (`keyijing.github.io`).

## Architecture

- **Layout inheritance**: `homepage.html` extends `default.html`. `default.html` is a minimal HTML shell; `homepage.html` adds the two-column (sidebar + content) structure.
- **Data-driven sidebar**: Author name, title, institution, and contacts are defined in `_data/homepage.yml` and rendered via Liquid (`site.data.homepage.author`).
- **Content separation**: Page content lives in Markdown (`index.md`); layout and styling are separate.
- **Icons**: Font Awesome 6 + Academicons loaded via CDN in `default.html`. Contact icons are icon-only (no text), displayed as a centered row.

## Styling Conventions

- Primary color `#0070f3` applied to **links only**, not headings.
- Headings use default text color with a `#ddd` bottom border.
- Contact icons are gray (`#555`), turning primary on hover.
- SCSS variables and CSS custom properties are both used (`$primary` / `--primary`).

## Key Files to Edit

| What to change | File |
|---|---|
| Author info, contacts | `_data/homepage.yml` |
| Page content | `index.md` |
| Site metadata | `_config.yml` |
| Styles / colors | `_sass/main.scss` |
| Layout structure | `_layouts/homepage.html` |
| Base HTML / CDN links | `_layouts/default.html` |

## Build

```bash
bundle exec jekyll build    # build
bundle exec jekyll serve    # local dev server at localhost:4000
```

Uses the `github-pages` gem for GitHub Pages compatibility.
