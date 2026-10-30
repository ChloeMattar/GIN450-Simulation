// Keep playback in view without moving keyboard focus away from the controls.
document.addEventListener('click', event => {
  const button = event.target.closest('button');
  if (!button || button.disabled) return;
  const shared = ['start', 'run-both', 'try-hot', 'try-normal'].includes(button.id);
  if (!shared && !button.classList.contains('run')) return;
  requestAnimationFrame(() => {
    const panel = shared ? document.querySelector('#panels > .proc') : button.closest('.proc');
    const target = panel?.querySelector('.diagram, .mem') || panel;
    const toolbar = document.querySelector('.toolbar');
    const scenario = document.querySelector('.scenario');
    const offset = (toolbar ? toolbar.getBoundingClientRect().height : 0) + (scenario ? scenario.getBoundingClientRect().height + 8 : 0) + 24;
    if (target) window.scrollTo({top: Math.max(0, window.scrollY + target.getBoundingClientRect().top - offset), behavior: 'instant'});
  });
}, true);

// Stack the DRAM message below its controls, including when controls wrap.
const stickyControls = document.querySelector('.dctl');
if (stickyControls) {
  const updateStickyHeight = () => document.documentElement.style.setProperty('--dram-controls-height', stickyControls.getBoundingClientRect().height + 'px');
  updateStickyHeight();
  new ResizeObserver(updateStickyHeight).observe(stickyControls);
}
