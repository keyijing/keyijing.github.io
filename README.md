# keyijing.github.io

Personal academic homepage built with Jekyll and hosted on GitHub Pages.

## Architecture

- **Layout inheritance**: `homepage.html` extends `default.html`. `default.html` is a minimal HTML shell; `homepage.html` adds the two-column (sidebar + content) structure.
- **Data-driven sections**: Author info, education, awards, and research are defined in `_data/homepage.yml` as structured data. Sidebar bio (title/institution) lives in `_includes/sidebar-bio.md` (Markdown, rendered via `markdownify`).
- **Content separation**: Page prose lives in Markdown (`index.md`); structured sections are rendered from YAML data in the layout.
- **Inline Markdown**: YAML text fields support Markdown (bold, links, math) via the `_includes/inline-md.html` helper.
- **Math rendering**: KaTeX loaded via CDN in `default.html` with auto-render for `$...$`, `$$...$$`, `\(...\)`, `\[...\]`.
- **Icons**: Font Awesome 6 + Academicons loaded via CDN in `default.html`. Contact icons are icon-only (no text), displayed as a centered row.
- **External links**: All links open in a new tab via `<base target="_blank">` in `default.html`.

## Structure

```
_config.yml          # Site-wide Jekyll settings (title, url, markdown, etc.)
_data/homepage.yml   # Structured data (author, education, awards, research)
_includes/
  sidebar-bio.md     # Sidebar bio (title, institution) in Markdown
  inline-md.html     # Reusable inline Markdown filter (markdownify + strip <p>)
_layouts/
  default.html       # Base HTML shell (head, CSS, icon CDNs, KaTeX, body)
  homepage.html      # Two-column layout: sidebar + structured sections
_sass/main.scss      # All styles (colors, layout, section entries, responsive)
assets/
  css/style.scss     # Jekyll SCSS entry point; imports main.scss
  img/profile1.png   # Profile photo
  pdf/               # Paper PDFs (linked from research entries)
index.md             # Homepage prose (About Me section)
Gemfile              # Ruby dependencies (github-pages gem)
```

## Customization

| What to change | File |
|---|---|
| Author name, contacts, pronunciation | `_data/homepage.yml` |
| Education, awards, research entries | `_data/homepage.yml` |
| Author title, institution | `_includes/sidebar-bio.md` |
| About Me prose | `index.md` |
| Site metadata | `_config.yml` |
| Profile photo | `assets/img/profile1.png` |
| Paper PDFs | `assets/pdf/` |
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
