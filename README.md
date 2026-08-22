# Generated Textbook PDFs

This branch contains the latest successfully built PDF snapshot for the
textbooks published by the [Undergraduate Mathematics Textbooks][repository]
project.

## Contents

PDFs are stored under [`pdf/`](pdf/) using stable textbook slugs as filenames.
The `.source-sha` file records the commit on `main` from which this snapshot was
built.

## How this branch is maintained

GitHub Actions creates and updates this branch after successful textbook builds
on `main`. Files may be replaced or removed on any update to keep the snapshot
consistent with `books.yml`.

Do not edit this branch directly. LaTeX sources, build configuration, issues,
and contributions are maintained on the [`main` branch][main]. Official
versioned publications, when available, are distributed through [GitHub
Releases][releases].

[repository]: https://github.com/sihyeon8240/math
[main]: https://github.com/sihyeon8240/math/tree/main
[releases]: https://github.com/sihyeon8240/math/releases
