# keyijing.github.io

Personal academic homepage built with Jekyll and hosted on GitHub Pages.

## Architecture

- **Layout inheritance**: `homepage.html` extends `default.html`. `default.html` is a minimal HTML shell; `homepage.html` adds the two-column (sidebar + content) structure.
- **Data-driven sidebar**: Author name and contacts are defined in `_data/homepage.yml`; title and institution live in `_includes/sidebar-bio.md` (Markdown, rendered via `markdownify`).
- **Content separation**: Page content lives in Markdown (`index.md`); layout and styling are separate.
- **Icons**: Font Awesome 6 + Academicons loaded via CDN in `default.html`. Contact icons are icon-only (no text), displayed as a centered row.

## Structure

```
_config.yml          # Site-wide Jekyll settings (title, url, markdown, etc.)
_data/homepage.yml   # Homepage content config (author name, contacts)
_includes/
  sidebar-bio.md     # Sidebar bio (title, institution) in Markdown
_layouts/
  default.html       # Base HTML shell (head, CSS, icon CDNs, body)
  homepage.html      # Two-column layout: sidebar + main content
_sass/main.scss      # All styles (colors, layout, responsive)
assets/
  css/style.scss     # Jekyll SCSS entry point; imports main.scss
  img/profile.svg    # Placeholder profile photo
index.md             # Homepage content (About, Education, Awards, Publications)
Gemfile              # Ruby dependencies (github-pages gem)
```

## Customization

| What to change | File |
|---|---|
| Author name, contacts | `_data/homepage.yml` |
| Author title, institution | `_includes/sidebar-bio.md` |
| Page content | `index.md` |
| Site metadata | `_config.yml` |
| Profile photo | `assets/img/profile.svg` |
| Styles / colors | `_sass/main.scss` |
| Layout structure | `_layouts/homepage.html` |
| Base HTML / CDN links | `_layouts/default.html` |

## Styling Conventions

- Primary color `#0070f3` applied to **links only**, not headings.
- Sidebar bio links inherit text color; primary color appears only on hover.
- Headings use default text color with a `#ddd` bottom border.
- Contact icons are gray (`#555`), turning primary on hover.
- SCSS variables and CSS custom properties are both used (`$primary` / `--primary`).

## Icons

Contact icons use [Font Awesome 6](https://fontawesome.com/) and [Academicons](https://jpswalsh.github.io/academicons/), loaded via CDN. Set the `icon` field in `_data/homepage.yml` to any valid class (e.g., `fas fa-envelope`, `fab fa-github`, `ai ai-google-scholar`).

## Local Development

```bash
bundle install
bundle exec jekyll serve    # local dev server at localhost:4000
bundle exec jekyll build    # production build
```

Uses the `github-pages` gem for GitHub Pages compatibility.
