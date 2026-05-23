# IJCAR'26 Camera-Ready Preparation Instructions

This document consolidates all official formatting, submission, licensing, and travel award guidelines retrieved from your Gmail account for **Submission #121**: *"Automatically Translating Proof Systems for SMT Solvers to the λΠ-calculus"*.

---

## 📅 Submission Deadline
> [!IMPORTANT]
> The (extended) deadline for both the **camera-ready copy** and the **license form** is **May 23rd, 2026 (AoE)** (due **TODAY/TOMORROW** depending on timezone).
> Submissions are uploaded via HotCRP: [https://submissions.floc26.org/ijcar/paper/121](https://submissions.floc26.org/ijcar/paper/121)

---

## 🛠️ Required Deliverables (HotCRP)

You must upload three items to your submission form:
1. **PDF of final version:** Upload near the top of the HotCRP submission page.
2. **ZIP file of article sources:** Upload towards the end of the form. Use the latest templates and follow the Springer guidelines.
3. **Signed License Form:** A signed PDF version of the Springer licensing agreement.
   * **License Form Template:** [https://home.uni-leipzig.de/clu/springer_license.docx](https://home.uni-leipzig.de/clu/springer_license.docx) (Pre-filled for IJCAR 2026).
   * Note: Articles are published under the **Springer Gold Open Access** scheme.

---

## 📐 Formatting & LaTeX Guidelines

### 1. Page Limits
* **Full Papers:** **15 pages** (excluding references and acknowledgements).
* **Short Papers:** **7 pages** (excluding references and acknowledgements).
* Templates and guidelines: [Springer Computer Science Proceedings Guidelines](https://www.springer.com/gp/computer-science/lncs/conference-proceedings-guidelines) (In particular, read the PDF *“Instructions for Proceedings Authors”*).

### 2. Mandatory "Disclosure of Interest" / Funding Section
Springer mandates that all authors disclose interest and funding.
* **If you have funding/acknowledgements:** Put them in the `Acknowledgements` section at the end of the paper.
* **If you do not have funding/competing interests:** Add a specific section at the end of the paper:
  ```latex
  \subsubsection{Disclosure of Interest}
  The authors have no competing interests to declare.
  ```
  *(Alternative one-line phrasing from the chairs: "The authors have no competing interests to declare that are relevant to the content of this article.")*
* **Note:** This statement does not count towards the page limit.

### 3. EU-Mandated "Alt Text" for Figures (Visual Impairments)
The EU mandates alternative text for all figures.
* **For Standard Images (`\includegraphics`):**
  Use the `alt` parameter:
  ```latex
  \begin{figure}
     \includegraphics[width=\textwidth,alt={alternative text}]{fig1.eps}
     \caption{A figure caption ...} \label{fig1}
  \end{figure}
  ```
* **For Custom TikZ Drawings / Complex Graphics:**
  If the `alt` parameter cannot be used directly (e.g., if rendering inline or via TikZ), declare the following macro in your preamble:
  ```latex
  \newcommand{\alttext}[2]{#2}
  ```
  And wrap the figure input or environment inside it, specifying the alt-text as the first parameter:
  ```latex
  \alttext{detailed description of the pipeline}{
      \input{fig-pipeline.tex}
  }
  ```
* **AI Fallback:** If you omit alternative text, Springer's production will use AI to auto-generate descriptions, which may lead to inaccurate interpretations of logical systems or mathematical diagrams.

---

## 🎓 Student Travel & Awards (Historical / Reference)

* **Woody Bledsoe Student Travel Awards:** Travel/registration support for student co-authors. Deadline was **May 21st, 2026** (contact: `ijcar2026@cs.uni-freiburg.de` with supervisor support letter).
* **Best Student Paper Award:** If the main author of the paper is a student, notify the chairs at `ijcar2026@cs.uni-freiburg.de` immediately.

---

## 📧 Email Source References

### 1. Late-Minute Figure Alt-Text & Funding Details (May 22, 2026)
> *From: Armin, Carsten, & Sara <ijcar2026@cs.uni-freiburg.de>*
> 
> "the new alt-text requirement described in Springer's author proceedings instructions we pointed at for graphics/figures raised some concerns, as particularly some authors asked us how to do this for full tikz plots etc.
>
> Even after some rounds of discussion with Springer we could not get a completely satisfactory answer. One suggestion from Springer was to come up with an artificial macro like `\alttext[2]{#2}` and encapsulate anything graphical which would benefit from alternative text. Then Springer's production process could pick that up from the sources (you can put the alternative text as first argument to that macro), e.g., as in `\alttext{unit-propagation}{\mathrel{\vdash\kern-.1ex{}_1}}` and similar for whole plots."
> 
> *(Message ID: 19e501bbd994144a)*

### 2. Travel Awards & Early Registration (May 8, 2026)
> *From: "IJCAR'26" <noreply@mail.submissions.floc26.org>*
> 
> "Springer mandates all authors to disclose interest, which requires you to list funding. That should be put into the acknowledgement section. If you do not have an acknowledgement nor funding section nor have to declare any other funding you should simply add a 'Disclosure of Interest' section at the end..."
> 
> *(Message ID: 19e080086f01aa40)*

### 3. Camera-Ready Submissions Opened (May 6, 2026)
> *From: "IJCAR'26" <noreply@mail.submissions.floc26.org>*
> 
> "congratulations again on having your article accepted to IJCAR 2026. Find below information on preparing the camera ready copy... All IJCAR 2026 articles will be published under the Springer gold open access scheme..."
> 
> *(Message ID: 19dfc8415c9c03a0)*
