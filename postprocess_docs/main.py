import os
from bs4 import BeautifulSoup

# Configuration
DOCS_DIR = os.path.join(os.path.dirname(__file__), "source/doc")
LANDING_TEXT_PATH = os.path.join(os.path.dirname(__file__), "landing_text.html")


def append_landing_text(soup):
    main = soup.find("main")
    if not main or soup.find(id="landing-text-fragment"):
        return

    if not os.path.exists(LANDING_TEXT_PATH):
        print(f"Warning: Landing text file {LANDING_TEXT_PATH} not found.")
        return

    with open(LANDING_TEXT_PATH, 'r', encoding='utf-8') as f:
        fragment_soup = BeautifulSoup(f, 'lxml')

    container = soup.new_tag("div", id="landing-text-fragment")
    fragment_root = fragment_soup.body or fragment_soup
    for child in list(fragment_root.contents):
        container.append(child)
    main.append(container)

def modify_html(file_path):
    """
    Parses a single HTML file and applies modifications.
    """
    print(f"Processing: {file_path}")
    
    with open(file_path, 'r', encoding='utf-8') as f:
        soup = BeautifulSoup(f, 'lxml') # 'lxml' is fast, or use 'html.parser'

    # --- START CUSTOMIZATIONS ---

    for link_text in ["foundational types", "tactics"]:
        for link in soup.find_all("a"):
            if link.get_text(strip=True) == link_text:
                link.decompose()
                break

    # Use recursive=False or filter for top-level modules to avoid 
    # decomposing children that are already gone.
    keep_paths = ["./LCS.html"] 
    module_list = soup.find("div", class_="module_list")
    if module_list:
        # We only want to remove the top-level library folders (e.g. Aesop, Mathlib)
        # finding only direct children details
        for ml in module_list.find_all("details", class_="nav_sect", recursive=False):
            if ml.get("data-path") not in keep_paths:
                ml.decompose()

    if os.path.basename(file_path) == "index.html":
        append_landing_text(soup)

    # --- END CUSTOMIZATIONS ---


    # Save the modified HTML back to the file
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(str(soup))

def main():
    if not os.path.exists(DOCS_DIR):
        print(f"Error: Directory {DOCS_DIR} not found.")
        return

    # Option A: Only modify specific files (recommended for speed)
    important_files = ["index.html", "navbar.html"]
    for filename in important_files:
        path = os.path.join(DOCS_DIR, filename)
        if os.path.exists(path):
            modify_html(path)

    """
    # Option B: Uncomment this to modify EVERY .html file in the directory
    for root, dirs, files in os.walk(DOCS_DIR):
        for name in files:
            if name.endswith(".html"):
                modify_html(os.path.join(root, name))
    """

if __name__ == "__main__":
    main()
