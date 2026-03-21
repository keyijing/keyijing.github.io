# keyijing.github.io

Personal academic homepage built with Jekyll and hosted on GitHub Pages.

## Structure

```
_config.yml          # Site-wide Jekyll settings (title, url, markdown, etc.)
_data/homepage.yml   # Homepage content config (author name, title, contacts)
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

- **Author info & contacts**: edit `_data/homepage.yml`
- **Homepage content**: edit `index.md`
- **Site title & URL**: edit `_config.yml`
- **Profile photo**: replace `assets/img/profile.svg`
- **Colors & styles**: edit `_sass/main.scss` (primary color defined at top)

## Icons

Contact icons use [Font Awesome 6](https://fontawesome.com/) and [Academicons](https://jpswalsh.github.io/academicons/), loaded via CDN. Set the `icon` field in `_data/homepage.yml` to any valid class (e.g., `fas fa-envelope`, `fab fa-github`, `ai ai-google-scholar`).

## Local Development

```bash
bundle install
bundle exec jekyll serve
```

Then visit `http://localhost:4000`.
